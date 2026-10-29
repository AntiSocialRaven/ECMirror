"""Endurance Coach - training log, load tracking, race predictions, plans and nutrition for any endurance sport.

Run:        python endurance.py
Self-test:  python endurance.py --selftest
Build EXE:  build.ps1
Data lives in %APPDATA%/EnduranceCoach/data.db, backed up to backups/ on every launch.
"""

import csv
import datetime as dt
import glob
import hashlib
import json
import math
import os
import re
import shutil
import sqlite3
import sys
import threading
import time
import xml.etree.ElementTree as ET

# ============================================================================
# FIXED - plumbing, formats and wire protocols. Changing these breaks things; rarely touched.
# ============================================================================

APP = "Endurance Coach"

DATA_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "EnduranceCoach")

DB_PATH = os.path.join(DATA_DIR, "data.db")

ONE = dt.timedelta(days=1)

KM_MI, KG_LB, M_FT, L_OZ, YD = 1.609344, 2.20462, 3.28084, 33.814, 0.9144

MODELLED = {"Swim", "Bike", "Run"}  # legs we can predict from thresholds; others use the race's goal time

DOW = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]

WMO = [
    (0, "Clear"),
    (1, "Mainly clear"),
    (2, "Partly cloudy"),
    (3, "Overcast"),
    (48, "Fog"),
    (55, "Drizzle"),
    (57, "Freezing drizzle"),
    (65, "Rain"),
    (67, "Freezing rain"),
    (77, "Snow"),
    (82, "Rain showers"),
    (86, "Snow showers"),
    (99, "Thunderstorms"),
]

WET = lambda code: 51 <= code <= 67 or 80 <= code <= 82 or code >= 95

ICY = lambda code: code in (56, 57, 66, 67) or 71 <= code <= 77 or code in (85, 86)

OUTDOOR = {"Run", "Bike", "Brick", "Walk", "Hike", "Ski", "Paddle", "Row", "Other"}

ISSUE_KINDS = ["Injury", "Illness", "Fatigue", "Other"]

SEVERITY = {1: "Niggle", 2: "Mild", 3: "Moderate", 4: "Severe", 5: "Can't train"}

DEFAULT_RAMP_DAYS = 14  # fallback for issues resolved before a ramp length was stored

RAMP_BASE_DAYS = {1: 5, 2: 7, 3: 10, 4: 14, 5: 21}  # floor on the graded return, by severity

LOWER = ["Run", "Hike", "Walk"]

ORDER = ["rest", "easy", "moderate", "normal", "push"]

STRAVA_TYPES = {
    "run": "Run",
    "trailrun": "Run",
    "virtualrun": "Run",
    "ride": "Bike",
    "virtualride": "Bike",
    "ebikeride": "Bike",
    "mountainbikeride": "Bike",
    "gravelride": "Bike",
    "emountainbikeride": "Bike",
    "velomobile": "Bike",
    "handcycle": "Bike",
    "swim": "Swim",
    "rowing": "Row",
    "virtualrow": "Row",
    "nordicski": "Ski",
    "backcountryski": "Ski",
    "rollerski": "Ski",
    "alpineski": "Ski",
    "hike": "Hike",
    "walk": "Walk",
    "snowshoe": "Hike",
    "kayaking": "Paddle",
    "canoeing": "Paddle",
    "standuppaddling": "Paddle",
    "weighttraining": "Strength",
    "crossfit": "Strength",
    "yoga": "Mobility",
    "pilates": "Mobility",
}

STRAVA_DATE_FORMATS = (
    "%b %d, %Y, %I:%M:%S %p",
    "%d %b %Y, %H:%M:%S",
    "%Y-%m-%d %H:%M:%S",
    "%Y-%m-%dT%H:%M:%SZ",
    "%m/%d/%Y %H:%M",
    "%d/%m/%Y %H:%M",
)

SPORT_FAMILY = {"Brick": "Bike"}

# Apple Health workout types -> app sports. `transition` (triathlon T1/T2) is skipped; unknown types become Other.
HEALTH_SPORTS = {
    **dict.fromkeys(["running", "runningTreadmill", "trackAndField", "wheelchairRunPace"], "Run"),
    **dict.fromkeys(["cycling", "bikingStationary", "handCycling"], "Bike"),
    **dict.fromkeys(["swimming", "swimmingPool", "swimmingOpenWater"], "Swim"),
    **dict.fromkeys(["rowing", "rowingMachine"], "Row"),
    **dict.fromkeys(["crossCountrySkiing", "skiing", "downhillSkiing", "snowSports"], "Ski"),
    **dict.fromkeys(["hiking", "snowshoeing"], "Hike"),
    **dict.fromkeys(["walking", "wheelchairWalkPace"], "Walk"),
    **dict.fromkeys(["paddleSports", "paddling"], "Paddle"),
    **dict.fromkeys(
        [
            "strengthTraining",
            "traditionalStrengthTraining",
            "functionalStrengthTraining",
            "weightlifting",
            "coreTraining",
        ],
        "Strength",
    ),
    **dict.fromkeys(
        ["yoga", "pilates", "flexibility", "stretching", "mindAndBody", "cooldown", "preparationAndRecovery"],
        "Mobility",
    ),
    "transition": None,
}

SCHEMA = """
CREATE TABLE IF NOT EXISTS workouts(id INTEGER PRIMARY KEY, date TEXT, sport TEXT, dur_s REAL, dist_km REAL,
    rpe REAL, avg_hr REAL, avg_w REAL, tss REAL, kcal REAL, notes TEXT);
CREATE TABLE IF NOT EXISTS wellness(date TEXT PRIMARY KEY, weight_kg REAL, sleep_h REAL, rhr REAL, hrv REAL,
    soreness INTEGER, stress INTEGER, notes TEXT);
CREATE TABLE IF NOT EXISTS kv(k TEXT PRIMARY KEY, v TEXT);
CREATE TABLE IF NOT EXISTS races(id INTEGER PRIMARY KEY, name TEXT, date TEXT, preset TEXT, legs TEXT,
    priority TEXT, temp_c REAL, t1 REAL, t2 REAL, goal_s REAL, result_s REAL, notes TEXT);
CREATE TABLE IF NOT EXISTS issues(id INTEGER PRIMARY KEY, kind TEXT, name TEXT, area TEXT, side TEXT, severity INTEGER,
    sports TEXT, start TEXT, "end" TEXT, notes TEXT, ramp_days INTEGER);
CREATE TABLE IF NOT EXISTS habits(id INTEGER PRIMARY KEY, uid TEXT, name TEXT, days TEXT, sort INTEGER, archived INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS habit_log(hkey TEXT PRIMARY KEY, habit TEXT, date TEXT, done INTEGER);
CREATE TABLE IF NOT EXISTS reminders(id INTEGER PRIMARY KEY, uid TEXT, title TEXT, time TEXT, days TEXT, active INTEGER DEFAULT 1);
CREATE TABLE IF NOT EXISTS quotes(id INTEGER PRIMARY KEY, uid TEXT, text TEXT, author TEXT);
CREATE TABLE IF NOT EXISTS scheduled(id INTEGER PRIMARY KEY, uid TEXT, date TEXT, time TEXT, sport TEXT, kind TEXT,
    dur_s REAL, dist_km REAL, notes TEXT);
CREATE TABLE IF NOT EXISTS gear(id INTEGER PRIMARY KEY, name TEXT, kind TEXT, sports TEXT, purchased TEXT,
    retire_km REAL, active INTEGER DEFAULT 1, is_default INTEGER DEFAULT 0, notes TEXT);
"""

DATA_TABLES = (
    "workouts",
    "wellness",
    "races",
    "issues",
    "habits",
    "habit_log",
    "reminders",
    "quotes",
    "scheduled",
    "gear",
)

GEAR_WARN_PCT = 90  # retire-at warning kicks in this close to the limit; 100+ is past it

# ---------------------------------------------------------------- sync (desktop hub <-> phones over Wi-Fi)
# Every synced row has a permanent id (uid; wellness uses its date), `updated` (ms, the edit time used for
# last-writer-wins) and `rev` (this database's change counter, used for "what changed since"). Triggers stamp
# them on every local write and record deletes as tombstones, so the app's normal write paths need no changes.
SYNC_TABLES = {
    "workouts": "uid",
    "races": "uid",
    "issues": "uid",
    "wellness": "date",
    "habits": "uid",
    "habit_log": "hkey",
    "reminders": "uid",
    "quotes": "uid",
    "scheduled": "uid",
    "gear": "uid",
}

LOCAL_KEYS = {
    "theme",
    "sync_host",
    "sync_code",
    "sync_remote_rev",
    "sync_pushed_rev",
    "sync_last",
    "hub_on",
    "hub_code",
    "hub_last",
    "health_on",
    "health_last",
    "watchfolder_path",
    "watchfolder_on",
    "watchfolder_last",
    "device_id",
    "device_name",
    "serve_assets",
}

NOW_MS = "CAST((julianday('now') - 2440587.5) * 86400000 AS INTEGER)"

LOCAL = "NOT EXISTS (SELECT 1 FROM kv WHERE k='applying')"

OLD_RACE_TYPES = {
    "Sprint": "Sprint triathlon",
    "Olympic": "Olympic triathlon",
    "70.3": "70.3 / half-distance triathlon",
    "140.6": "Ironman / full-distance triathlon",
}

LIFE_KEYS = [
    "wake_weekday",
    "wake_weekend",
    "school_days",
    "sleep_goal",
    "winddown",
    "notify_bedtime",
    "notify_checkin",
    "checkin_time",
    "notify_nudge",
    "nudge_time",
    "brief_min",
]

# ---------------------------------------------------------------- sync: being a client of another device's hub
# The phone drives this from bridge.js with native HTTP. A second computer needs the same thing in Python, so a
# laptop pairs with the desktop exactly the way a phone does: one hub, every other device a client of it.
# ---------------------------------------------------------------- finding a hub by name instead of by address
# Reading an IP address off one screen and typing it into another was always the wrong interface: it is an
# implementation detail, and DHCP invalidates it without telling anyone. A hub now advertises itself over mDNS
# and clients browse for it, so devices are found by name, on any network, and keep working when the router
# moves them. The subnet sweep further down survives only as a last resort for networks that block multicast.
SERVICE_TYPE = "_endurancecoach._tcp.local."

SYNC_PORTS = (8977, 8978, 8979)  # the hub takes the next free port if 8977 is busy

IS_PHONE = sys.platform == "emscripten"  # Pyodide: the iPhone build runs the engine in the browser

# ---------------------------------------------------------------- handing the UI and engine to the phone
# The phone runs this exact engine and this exact UI, but it gets them inside an App Store build, so every
# change to either one costs a build. It does not have to: both are plain text the phone already fetches at
# runtime, so a hub can simply hand over the copies it is running and the phone can use those instead.
#
# That makes editing ui.html on this PC show up on the phone with a pull-to-refresh. It is off by default -
# serving files is not what a sync hub is for - and it only ever serves these two, by exact name.
ASSET_FILES = ("ui.html", "endurance.py")

# ---------------------------------------------------------------- updating itself from GitHub releases
# The desktop app ships as one unsigned exe, so there is no store to update it. It asks GitHub what the latest
# release is, and - only when the athlete clicks - downloads that release's exe and swaps itself for it.
#
# Nothing is downloaded or run without being asked for: a background check only ever reports a version number.
# Windows will not let a running exe be overwritten, but it will let one be renamed, so the swap is: write the
# new build alongside, rename the running one out of the way, move the new one into its place, and clear the
# leftover on the next launch.
# a public mirror: this source repo is private, and the updater cannot read a private repo's releases
UPDATE_REPO = "AntiSocialRaven/ECMirror"

RELEASES_API = f"https://api.github.com/repos/{UPDATE_REPO}/releases/latest"

ASSET_NAME = "EnduranceCoach.exe"


# ============================================================================
# TUNABLE - reference times, tiers, presets, defaults, wording. Edit freely.
# ============================================================================

VERSION = "1.1.0"  # the release workflow checks the v* tag against this

ALL_SPORTS = ["Swim", "Bike", "Run", "Brick", "Row", "Ski", "Hike", "Walk", "Paddle", "Strength", "Mobility", "Other"]

LEG_SPORTS = ["Swim", "Bike", "Run", "Row", "Ski", "Hike", "Paddle", "Other"]

PRESETS = {  # name -> (group, [(sport, km)])
    "Sprint triathlon": ("Triathlon", [("Swim", 0.75), ("Bike", 20), ("Run", 5)]),
    "Olympic triathlon": ("Triathlon", [("Swim", 1.5), ("Bike", 40), ("Run", 10)]),
    "70.3 / half-distance triathlon": ("Triathlon", [("Swim", 1.9), ("Bike", 90), ("Run", 21.1)]),
    "Ironman / full-distance triathlon": ("Triathlon", [("Swim", 3.8), ("Bike", 180.2), ("Run", 42.2)]),
    "Sprint duathlon": ("Duathlon", [("Run", 5), ("Bike", 20), ("Run", 2.5)]),
    "Standard duathlon": ("Duathlon", [("Run", 10), ("Bike", 40), ("Run", 5)]),
    "Aquabike (half)": ("Duathlon", [("Swim", 1.9), ("Bike", 90)]),
    "5K": ("Run", [("Run", 5)]),
    "10K": ("Run", [("Run", 10)]),
    "Half marathon": ("Run", [("Run", 21.0975)]),
    "Marathon": ("Run", [("Run", 42.195)]),
    "50K ultra": ("Run", [("Run", 50)]),
    "50-mile ultra": ("Run", [("Run", 80.47)]),
    "100K ultra": ("Run", [("Run", 100)]),
    "100-mile ultra": ("Run", [("Run", 160.93)]),
    "40K time trial": ("Bike", [("Bike", 40)]),
    "Gran fondo (120 km)": ("Bike", [("Bike", 120)]),
    "Century (100 mi)": ("Bike", [("Bike", 160.93)]),
    "1500 m swim": ("Swim", [("Swim", 1.5)]),
    "5K open-water swim": ("Swim", [("Swim", 5)]),
    "10K open-water swim": ("Swim", [("Swim", 10)]),
    "Rowing 2K": ("Other", [("Row", 2)]),
    "Rowing half marathon": ("Other", [("Row", 21.0975)]),
    "XC ski marathon": ("Other", [("Ski", 42)]),
    "Custom": ("Custom", [("Run", 10)]),
}

DEFAULTS = dict(
    name="",
    units="imperial",
    sex="M",
    age=30,
    weight_kg=75.0,
    height_cm=178.0,
    sports=["Swim", "Bike", "Run", "Strength"],
    ftp=200.0,
    lthr=165.0,
    max_hr=188.0,
    rest_hr=55.0,
    hr_model="lthr",
    run_thr_pace=300.0,
    css=115.0,
    recent_race_km=0.0,
    recent_race_s=0.0,
    cda=0.30,
    bike_kg=10.0,
    plan_start=dt.date.today().isoformat(),
    weekly_hours=7.0,
    peak_hours=12.0,
    days_per_week=6,
    long_day=6,
    recovery_every=4,
    taper_weeks=0,
    strength=True,
    plan_race="",
    goal="maintain",
    activity="light",
    protein_gkg=0.0,
    gut_carbs=75.0,
    gel_carbs=25.0,
    sweat_rate=1.0,
    sweat_na=900.0,
    caffeine_mg=0.0,
    caffeine_sensitivity="normal",
    theme="system",
    checklist=[],
    setup_done=False,
    sync_host="",
    sync_code="",
    sync_remote_rev=0,
    sync_pushed_rev=0,
    sync_last="",
    hub_on=False,
    hub_code="",
    hub_last="",
    serve_assets=False,
    device_id="",
    device_name="",
    health_on=False,
    health_last="",
    watchfolder_path="",
    watchfolder_on=False,
    watchfolder_last="",
    team_on=False,
    team_days=[0, 1, 2, 3, 4],
    team_min=90.0,
    team_label="Team practice",
    team_sport="Run",
    wake_weekday="06:30",
    wake_weekend="08:00",
    wake_once={},
    school_days=[0, 1, 2, 3, 4],
    sleep_goal=0.0,
    winddown=30,
    notify_bedtime=True,
    notify_checkin=True,
    checkin_time="07:00",
    notify_nudge=True,
    nudge_time="19:00",
    brief_min=45,
    home_place="",
    home_lat=0.0,
    home_lon=0.0,
    train_time="07:00",
    team_time="15:30",
)

LIN = {
    "dist": (1 / KM_MI, "km", "mi"),
    "weight": (KG_LB, "kg", "lb"),
    "height": (1 / 2.54, "cm", "in"),
    "elev": (M_FT, "m", "ft"),
    "vol": (L_OZ, "L", "oz"),
}

MET = {
    "Swim": 8,
    "Bike": 8,
    "Run": 10,
    "Brick": 9,
    "Row": 8.5,
    "Ski": 9,
    "Hike": 6,
    "Walk": 4,
    "Paddle": 6,
    "Strength": 5,
    "Mobility": 2.5,
    "Other": 6,
}

# Open-class references (seconds), men then women. Running: world records - track for the mile/5K/10K, road for
# the half and marathon. Swimming: long-course freestyle world records. Plain constants: edit when a record falls.
REF_TIMES = {
    ("Run", "1mi"): (223.13, 247.64),
    ("Run", "2mi"): (474.10, 538.58),
    ("Run", "5k"): (755.36, 840.21),
    ("Run", "10k"): (1571.0, 1734.14),
    ("Run", "half"): (3402.0, 3772.0),
    ("Run", "mar"): (7235.0, 7796.0),
    ("Swim", "100m"): (46.40, 51.71),
    ("Swim", "400m"): (220.0, 235.0),
    ("Swim", "1500m"): (871.0, 920.5),
    ("Row", "2k"): (335.8, 381.1),  # 2 km erg world records (Concept2), not on-water
    # Bike: the UCI hour record (56.79 km men, 50.46 km women) carried to each distance with a fatigue decay -
    # 59 / 56.8 / 51.5 / 49 km/h for 20 / 40 / 100 / 160 km, women at the hour-record ratio. Pure time-trial speeds.
    # ponytail: a road race is drafted, hilly or both, so a good result there reads low (or high, in a peloton)
    # against these; the page says so. Course-adjusting would need elevation and wind per ride.
    ("Bike", "20k"): (1220.0, 1373.0),
    ("Bike", "40k"): (2535.0, 2854.0),
    ("Bike", "100k"): (6990.0, 7868.0),
    ("Bike", "160k"): (11755.0, 13232.0),
}

RECORD_EVENTS = [  # sport, key, label, km - the distances a best effort is hunted for
    ("Run", "1mi", "1 mile", 1.609344),
    ("Run", "2mi", "2 mile", 3.218688),
    ("Run", "5k", "5K", 5.0),
    ("Run", "10k", "10K", 10.0),
    ("Run", "half", "Half marathon", 21.0975),
    ("Run", "mar", "Marathon", 42.195),
    ("Swim", "100m", "100 m", 0.1),
    ("Swim", "400m", "400 m", 0.4),
    ("Swim", "1500m", "1500 m", 1.5),
    ("Row", "2k", "2 km", 2.0),
    ("Bike", "20k", "20 km ride", 20.0),
    ("Bike", "40k", "40 km ride", 40.0),
    ("Bike", "100k", "100 km ride", 100.0),
    ("Bike", "160k", "160 km ride", 160.0),
]

# Threshold references: world-class sustainable output. Run = the one-hour run records (21.33 km / 18.93 km) as
# s/km; swim = world-record 1500 pace as s/100 m; bike = the top row of the Coggan power profile, W/kg at FTP.
REF_THRESHOLD = {("Run", "thr"): (168.8, 190.2), ("Swim", "thr"): (58.1, 61.4), ("Bike", "thr"): (6.44, 5.69)}

# Coggan/Allen power profile, FTP column: W/kg -> score, so the chart's own category names line up with the
# tiers (Cat 5 ~ Iron, Cat 4 ~ Bronze, Cat 3 ~ Silver, Cat 2 ~ Gold, Cat 1 ~ Platinum). The anchor scores below
# are paired to TIERS' own boundaries one-for-one - see the note above TIERS for why they moved.
COGGAN = {
    "M": [(2.21, 25), (2.79, 35), (3.47, 47), (4.20, 58), (4.94, 70), (5.69, 82), (6.44, 100)],
    "F": [(1.80, 25), (2.26, 35), (2.90, 47), (3.60, 58), (4.30, 70), (5.03, 82), (5.69, 100)],
}

COGGAN_LABEL = [
    (25, "Cat 5 / untrained"),
    (35, "Cat 4"),
    (47, "Cat 3"),
    (58, "Cat 2"),
    (70, "Cat 1"),
    (82, "Exceptional"),
    (100, "World class"),
]

# Age factor: what share of an open-class athlete's standard applies at this age - 1.0 through the peak years
# (20-30), under 1.0 for juniors and masters so both get credit for racing off peak.
# ponytail: one piecewise curve approximating the WMA distance-running tables, which differ a little by sex and
# event. Drop in the published per-event factors if these grades ever need to be official.
AGE_CURVE = [
    (8, 0.72),
    (10, 0.79),
    (12, 0.85),
    (14, 0.90),
    (16, 0.945),
    (18, 0.975),
    (20, 1.0),
    (30, 1.0),
    (35, 0.983),
    (40, 0.954),
    (45, 0.918),
    (50, 0.874),
    (55, 0.827),
    (60, 0.775),
    (65, 0.717),
    (70, 0.655),
    (75, 0.586),
    (80, 0.510),
    (85, 0.430),
    (90, 0.345),
    (100, 0.20),
]

# Tier bands on the score, carrying running's age-grade class names. Three divisions inside each band (III at the
# bottom, I at the top) give a visible next step: Gold III -> Gold II -> Gold I -> Platinum III.
#
# The scale is still anchored on the literal world record (grade_time: ref/actual*100, so matching the WR exactly
# is 100) - that part is sound and worth keeping, since it is the one truly objective, unfakeable reference point
# this app has, with no backend and no real leaderboard to grade against instead. But banding that scale evenly
# in tens (50/60/70/80/90) packed nearly all of real human achievement into Iron through Silver: even a 15:00 5K,
# itself a genuinely elite open adult time, only cleared Platinum, while Diamond and Elite sat reserved for
# performances within a few percent of the outright world record - i.e. for nobody who isn't a professional
# record-holder. A locally competitive runner, clearly ahead of most of a real field, read as barely above
# Iron. These bands are re-spaced so a strong-but-human performance lands where it reads as strong.
TIERS = [
    ("Iron",     0,  34, "", "#8a919c"),
    ("Bronze",  34,  44, "", "#b5783c"),
    ("Silver",  44,  53, "", "#9aa5b1"),
    ("Gold",    53,  61, "", "#d9a521"),
    ("Platinum",61,  68, "", "#2fb8bf"),
    ("Emerald", 68,  75, "", "#17b26a"),
    ("Ruby",    75,  82, "", "#e03131"),
    ("Diamond", 82,  89, "", "#4f8dff"),
    ("Elite",   89, None, "World Class", "#b45bff"),
]

WINDOW_SLACK = 1.15  # how far a block of splits may overshoot the target before it stops counting as that effort

# Multisport: one reference total per standard distance, men then women. Unlike a track record these are far
# more course-dependent - wetsuit and current on the swim, elevation and draft-legal racing on the bike - so the
# page says so and the rank is a guide, not a stopwatch. Approximate world-best performances.
MULTI_EVENTS = [  # key, label, the PRESETS entry whose legs it matches, reference total
    ("tri_sprint", "Sprint triathlon", "Sprint triathlon", (3060, 3390)),
    ("tri_oly", "Olympic triathlon", "Olympic triathlon", (6240, 6840)),
    ("tri_70", "70.3 / half-distance", "70.3 / half-distance triathlon", (12544, 13890)),
    ("tri_full", "Ironman / full-distance", "Ironman / full-distance triathlon", (26600, 28960)),
    ("du_sprint", "Sprint duathlon", "Sprint duathlon", (3120, 3480)),
    ("du_std", "Standard duathlon", "Standard duathlon", (6300, 7020)),
    ("aquabike", "Aquabike (half)", "Aquabike (half)", (7700, 8600)),
]

# A run off the bike is not a standalone run, so it is graded against world-class triathlon run splits instead
# of track records. The gap widens with distance, which is the bike fatigue showing up.
REF_OFF_BIKE = {5.0: (870, 990), 10.0: (1740, 1950), 21.0975: (4080, 4560), 42.195: (9000, 9840)}

OFF_BIKE_LABEL = {
    5.0: "5K off the bike",
    10.0: "10K off the bike",
    21.0975: "Half marathon off the bike",
    42.195: "Marathon off the bike",
}

# (weekday Mon=0, key, sport, share of weekly hours, typical IF, priority 1=key session)
TEMPLATES = {
    "tri": [
        (0, "swim_easy", "Swim", 0.06, 0.65, 3),
        (1, "bike_q", "Bike", 0.15, 0.85, 1),
        (1, "run_easy", "Run", 0.07, 0.70, 4),
        (2, "swim_q", "Swim", 0.10, 0.80, 2),
        (2, "run_q", "Run", 0.10, 0.85, 1),
        (3, "bike_mid", "Bike", 0.12, 0.75, 2),
        (4, "swim_end", "Swim", 0.08, 0.72, 3),
        (5, "long_bike", "Bike", 0.22, 0.72, 1),
        (6, "long_run", "Run", 0.12, 0.72, 1),
    ],
    "run": [
        (1, "run_q", "Run", 0.16, 0.88, 1),
        (2, "run_easy", "Run", 0.12, 0.70, 3),
        (3, "run_tempo", "Run", 0.15, 0.85, 1),
        (4, "run_easy", "Run", 0.10, 0.68, 4),
        (5, "run_strides", "Run", 0.13, 0.70, 3),
        (6, "long_run", "Run", 0.34, 0.74, 1),
    ],
    "bike": [
        (1, "bike_q", "Bike", 0.17, 0.88, 1),
        (2, "bike_easy", "Bike", 0.12, 0.62, 4),
        (3, "bike_mid", "Bike", 0.17, 0.80, 1),
        (5, "bike_end", "Bike", 0.20, 0.70, 2),
        (6, "long_bike", "Bike", 0.34, 0.72, 1),
    ],
    "swim": [
        (0, "swim_easy", "Swim", 0.14, 0.65, 3),
        (1, "swim_q", "Swim", 0.20, 0.82, 1),
        (2, "swim_end", "Swim", 0.18, 0.72, 2),
        (3, "swim_easy", "Swim", 0.12, 0.65, 4),
        (4, "swim_q", "Swim", 0.16, 0.82, 1),
        (6, "swim_long", "Swim", 0.20, 0.72, 1),
    ],
    "du": [
        (1, "bike_q", "Bike", 0.17, 0.85, 1),
        (2, "run_easy", "Run", 0.10, 0.70, 3),
        (3, "run_q", "Run", 0.15, 0.86, 1),
        (4, "bike_easy", "Bike", 0.10, 0.62, 4),
        (5, "long_bike", "Bike", 0.26, 0.72, 1),
        (6, "long_run", "Run", 0.22, 0.73, 1),
    ],
    "aquabike": [
        (0, "swim_easy", "Swim", 0.10, 0.65, 3),
        (1, "bike_q", "Bike", 0.18, 0.85, 1),
        (2, "swim_q", "Swim", 0.14, 0.80, 1),
        (3, "bike_mid", "Bike", 0.16, 0.76, 2),
        (4, "swim_end", "Swim", 0.12, 0.72, 2),
        (6, "long_bike", "Bike", 0.30, 0.72, 1),
    ],
    "generic": [
        (1, "gen_q", "*", 0.18, 0.86, 1),
        (2, "gen_easy", "*", 0.14, 0.68, 3),
        (3, "gen_tempo", "*", 0.18, 0.80, 1),
        (5, "gen_easy", "*", 0.15, 0.68, 3),
        (6, "gen_long", "*", 0.35, 0.72, 1),
    ],
}

DESC = {
    "swim_easy": {
        "Recovery": "Easy swim, drills only. Relaxed.",
        "*": "Technique swim: drills (catch-up, scull, 6-kick switch) then easy @ {css_easy}.",
    },
    "swim_q": {
        "Base": "CSS set: 8-10 x 100 @ {cssp}, 15 s rest.",
        "Build": "CSS set: 3 x (4x200 @ CSS+2s, 20 s rest), 1 min between rounds.",
        "Peak": "Race-pace set: 3 x 400 @ race effort, 45 s rest. Sight every 6-8 strokes.",
        "Taper": "6x100 @ {cssp} with full rest. Short and sharp.",
        "Recovery": "Easy swim, drills.",
    },
    "swim_end": {
        "Base": "Endurance: 4x400 steady @ {css_easy}, 30 s rest.",
        "Build": "Endurance: 3x600 @ CSS+3s, pull buoy on the last one.",
        "Peak": "Continuous 2000-2500 steady. Practise starts and sighting.",
        "*": "Easy aerobic swim @ {css_easy}.",
    },
    "swim_long": {
        "Base": "Long aerobic swim, continuous or 5x500 @ {css_easy}.",
        "Build": "Long swim: 2 x 1000 @ CSS+4s, 1 min rest.",
        "Peak": "Race-distance rehearsal at goal effort, ideally in open water with feeding practice.",
        "*": "Steady aerobic swim @ {css_easy}.",
    },
    "bike_q": {
        "Base": "Sweet spot: 3x10 min @ {ssw}, 5 min easy between; rest Z2 {z2w}. Cadence 85-95.",
        "Build": "Threshold: 3x12-15 min @ {thrw}, 5 min recoveries.",
        "Peak": "Race-specific: 2x20-25 min @ {racew} + 4x3 min @ {vo2w}.",
        "Taper": "3x8 min @ {racew}. Keep sharpness, drop volume.",
        "Recovery": "Easy spin Z1-Z2 {z2w} with a few high-cadence spin-ups.",
    },
    "bike_mid": {
        "Base": "Endurance Z2 @ {z2w} with 3x5 min high cadence (100+).",
        "Build": "Tempo: 2x20 min @ {racew}, race position.",
        "Peak": "Endurance with 3x10 min @ {racew}. Rehearse race fueling.",
        "*": "Easy endurance ride Z2 @ {z2w}.",
    },
    "bike_easy": {"*": "Recovery spin 45-60 min Z1 (under {z1w}). Legs should feel better after."},
    "bike_end": {
        "Base": "Endurance ride Z2 @ {z2w}.",
        "Build": "Endurance ride with 30 min @ tempo {tempow}.",
        "Peak": "Endurance ride with 2x15 min @ {racew}.",
        "*": "Easy endurance ride Z2 @ {z2w}.",
    },
    "long_bike": {
        "Base": "Long ride Z2 @ {z2w}. Fuel ~60 g carbs/h. Extend duration gradually.",
        "Build": "Long ride Z2, last 45-60 min @ {racew}.{brick} Fuel {carbs} g carbs/h.",
        "Peak": "Race simulation: long ride with 2x45 min @ {racew}.{brick} Full race kit + nutrition.",
        "Taper": "60-90 min with 20 min @ {racew}.",
        "Recovery": "Easy ride Z1-Z2. Coffee stop allowed.",
    },
    "run_easy": {
        "Recovery": "Easy 20-30 min jog @ {easy}, or skip if sore.",
        "*": "Easy run Z2 @ {easy}, conversational.",
    },
    "run_strides": {"*": "Easy run Z2 @ {easy} finishing with 6 x 20 s strides (fast, relaxed, full recovery)."},
    "run_q": {
        "Base": "Hills: 8 x 60 s uphill hard, jog down. Builds strength and economy.",
        "Build": "Threshold: 3-4 x 8 min @ {thr}, 2 min jog.",
        "Peak": "VO2 / race sharpening: 5 x 3 min @ {vo2p}, 2 min jog, or race-pace blocks @ {race_run}.",
        "Taper": "3 x 5 min @ {race_run}, easy otherwise.",
        "Recovery": "Easy run Z2 @ {easy}.",
    },
    "run_tempo": {
        "Base": "Steady: 20-30 min Z3 @ {steady} inside an easy run.",
        "Build": "Tempo: 25-35 min continuous @ {thr} to {steady}.",
        "Peak": "Race-pace run: 2 x 20 min @ {race_run}.",
        "Taper": "15 min @ {race_run} inside an easy run.",
        "Recovery": "Easy run Z2 @ {easy}.",
    },
    "long_run": {
        "Base": "Long run Z2 @ {easy}. Grow it no more than ~10%/week.",
        "Build": "Long run Z2 @ {easy}, last 20 min @ {steady}. Practise fueling.",
        "Peak": "Long run with 3 x 15 min @ {race_run}. Rehearse race shoes, kit and gels.",
        "Taper": "Shorter long run, easy, with 10 min @ {race_run}.",
        "Recovery": "Easy run @ {easy}.",
    },
    "gen_q": {
        "Base": "{sport}: 6 x 3 min hard (Z4, {hr4}) with 2 min easy.",
        "Build": "{sport}: 4 x 8 min at threshold (Z4, {hr4}), 3 min easy.",
        "Peak": "{sport}: race-pace blocks, 3 x 10 min at goal effort.",
        "Taper": "{sport}: short, 4 x 2 min at race effort.",
        "Recovery": "{sport}: easy Z1-Z2 ({hr2}).",
    },
    "gen_tempo": {
        "*": "{sport}: 2 x 15 min tempo (Z3), rest aerobic Z2 ({hr2}).",
        "Recovery": "{sport}: easy Z2 ({hr2}).",
    },
    "gen_easy": {"*": "{sport}: easy aerobic Z2 ({hr2}), smooth technique."},
    "gen_long": {
        "Base": "{sport}: long aerobic session Z2 ({hr2}). Build duration gradually.",
        "Build": "{sport}: long session Z2 with the last 20 min at race effort.",
        "Peak": "{sport}: race simulation at goal effort with race fueling.",
        "*": "{sport}: aerobic Z2 ({hr2}).",
    },
}

RACE_WEEK_DESC = {
    "Swim": "Short swim with 4 x 100 at race effort. Stay loose.",
    "Bike": "Openers: 3 x 3 min at race effort, rest easy.",
    "Run": "Easy run with 4 x 20 s strides.",
    "*": "Short and easy with a few 1-min race-effort pickups.",
}

PHASE_FOCUS = {
    "Base": "Aerobic engine, technique, strength. Mostly Z2.",
    "Build": "Threshold work and race-specific sessions.",
    "Peak": "Race simulations at goal pace; rehearse nutrition and kit.",
    "Recovery": "Absorb the training. Easy volume only.",
    "Taper": "Volume down, keep some intensity.",
    "Race week": "Stay fresh, fuel up, execute.",
}

TEAM_TAG = "Team practice"

# ---------------------------------------------------------------- sessions the athlete schedules themselves
# kind -> (intensity factor, run pace as a multiple of threshold pace (slow end, fast end), heart-rate zone index)
SCHED_KINDS = {
    "Easy": (0.70, (1.29, 1.14), 1),
    "Long": (0.72, (1.29, 1.14), 1),
    "Recovery": (0.62, (1.45, 1.29), 0),
    "Tempo": (0.85, (1.13, 1.06), 2),
    "Intervals": (0.88, (0.99, 0.94), 4),
    "Race pace": (0.90, (1.05, 1.0), 3),
}

SCHED_DETAIL = {
    "Easy": "conversational, Z2",
    "Long": "steady Z2 the whole way; practise your fueling",
    "Recovery": "very easy, shorter than you think",
    "Tempo": "comfortably hard, Z3, after a 10-15 min warm-up",
    "Intervals": "hard reps with easy recoveries, after a 15 min warm-up",
    "Race pace": "blocks at goal race effort",
}

PACED = {"Run": 1.0, "Walk": 2.3, "Hike": 2.8}  # rough pace multiples for sports that can be timed from a distance

SEVERITY_HELP = {
    1: "Train as planned, keep it easy and watch it.",
    2: "Shorter, easier sessions in the affected sports.",
    3: "Affected sports swapped for cross-training.",
    4: "Cross-training only, reduced volume.",
    5: "Rest and rehab only.",
}

BODY = {  # area -> default restricted sports, rehab, when to get it checked
    "Ankle": (
        LOWER,
        "Ankle circles and alphabet, towel scrunches; once walking is pain-free: calf raises (two legs, then one) and single-leg balance, eyes open then closed.",
        "Get it checked if you couldn't take 4 steps straight after the injury or can't now, if the bony back edge or tip of either ankle bone or the base of the 5th toe bone is tender to press, or if swelling and bruising are severe.",
    ),
    "Foot / plantar": (
        LOWER,
        "Towel scrunches, rolling the arch on a ball, calf stretches, slow single-leg calf raises.",
        "Get it checked if pain is sharp and pinpoint on a bone, or worse at rest or at night (possible stress fracture).",
    ),
    "Achilles / calf": (
        LOWER,
        "Isometric calf holds (5 x 45 s), then slow heavy calf raises straight- and bent-knee as pain allows.",
        "Get it checked urgently if you felt a pop or kick at the back of the ankle or can't rise onto your toes.",
    ),
    "Shin": (
        LOWER,
        "Calf raises, tibialis raises against a wall, hip and glute work. Swap impact for bike or pool.",
        "Get it checked if the pain is pinpoint on the bone, hurts to hop, or aches at rest or at night (possible stress fracture).",
    ),
    "Knee": (
        LOWER + ["Bike"],
        "Quad sets, straight-leg raises, glute bridges, side-lying leg raises, step-downs within a pain-free range.",
        "Get it checked if the knee swelled quickly, locks or gives way, or you can't straighten it fully.",
    ),
    "Hip / groin": (
        LOWER,
        "Glute bridges, clamshells, side planks, gentle adductor squeezes.",
        "Get it checked if there's deep groin pain on weight-bearing or pain at night (possible stress fracture).",
    ),
    "Hamstring": (
        ["Run"],
        "Isometric bridge holds, then bridges and Nordic lowers progressed slowly; no stretching into pain early on.",
        "Get it checked if there was a pop, large bruising, or you can't walk normally.",
    ),
    "IT band / outer knee": (
        LOWER,
        "Hip abductor work (side-lying raises, banded walks), glute bridges, foam-roll the outer thigh (not the knee).",
        "",
    ),
    "Lower back": (
        ["Run", "Row"],
        "Walking, cat-cow, bird-dog, dead bug, glute bridges. Stay gently active.",
        "Get urgent care for numbness in the groin or saddle area, bladder or bowel changes, or leg weakness.",
    ),
    "Shoulder": (
        ["Swim", "Row", "Paddle", "Ski"],
        "Band external rotations, scapular retraction, wall slides within a pain-free range.",
        "Get it checked if you can't lift the arm, it looks deformed, or there's numbness down the arm.",
    ),
    "Wrist / hand": (
        ["Row", "Paddle", "Ski"],
        "Gentle range of motion, grip squeezes as pain allows.",
        "Get it checked if there's bony tenderness at the base of the thumb (possible scaphoid fracture).",
    ),
    "Other": (
        [],
        "Gentle pain-free mobility and strength for the area.",
        "Get it checked if it's not clearly improving within 1-2 weeks.",
    ),
}

KIND_GUIDANCE = {
    "Injury": [
        "First 2-3 days: protect it, elevate it and use gentle compression. Avoid anything that sharply increases pain.",
        "Then load it gradually: pain up to about 3/10 during exercise is acceptable if it has settled by the next morning.",
        "Keep fitness with pain-free cross-training. The plan swaps affected sessions automatically.",
    ],
    "Illness": [
        "Neck check: symptoms only above the neck (runny nose, mild sore throat) mean easy exercise is fine if you feel up to it.",
        "Fever, chest symptoms, body aches or stomach bugs mean rest. Don't train through a fever.",
        "Return once you've been symptom-free for 24-48 h, starting easy. The plan ramps you back over 2 weeks.",
    ],
    "Fatigue": [
        "Protect sleep (8+ h in bed), eat enough carbohydrate, and drop intensity before you drop volume.",
        "Persistent fatigue is often under-fuelling (RED-S), low iron or ferritin, low vitamin D, illness, or life stress.",
        "If it doesn't lift after 2-3 weeks of lighter training, see a doctor and ask for bloodwork (full blood count, ferritin, vitamin D, thyroid).",
    ],
    "Other": ["Adjust training around it and note what helps. See a professional if it isn't improving."],
}

SWAP = {
    "Run": ["Bike", "Swim", "Row", "Ski", "Paddle"],
    "Bike": ["Swim", "Run", "Row"],
    "Swim": ["Bike", "Run", "Row"],
    "Row": ["Bike", "Swim", "Run"],
    "Hike": ["Bike", "Swim"],
    "Walk": ["Bike", "Swim"],
}

SWAP_DESC = {
    "Bike": "Bike (indoor trainer is fine)",
    "Swim": "Pool session: swim, or aqua jog if you're a runner",
    "Row": "Rowing erg",
    "Run": "Run",
    "Ski": "Ski / ski erg",
    "Paddle": "Paddle",
}

# ---------------------------------------------------------------- what the coach says
# The plan templates have always kept their prose in a catalog keyed by session and phase (see DESC below);
# the advisory layer grew its sentences inline instead. These are the same idea: an id, a template, and the
# numbers filled in at the point of use, so the wording can be rewritten - or swapped for another voice, or
# translated - without reading the logic that decides which line applies.
#
# Keys are stable identifiers and are never shown. Values are str.format templates. Anything that is not
# prose - SQL, column names, sport names that are also database values - stays where it is on purpose.
COPY = {
    # why today is what it is. Ordered loosely by how decisive the reason tends to be.
    "advice.issue": "{name} is active ({severity})",
    "advice.streak.many": "{n} hard days back to back - that is where injuries come from",
    "advice.streak.owed": "Two hard days in a row and {hours:.0f} h of recovery still owed",
    "advice.streak.two": "Two hard days in a row already",
    "advice.recovery.deep": "{hours:.0f} h of recovery still owed from the last few sessions",
    "advice.recovery.some": "{hours:.0f} h of recovery still owed",
    "advice.recovery.tail": "{hours:.0f} h of recovery left to run down",
    "advice.rest.none": "{n} days straight without a day off",
    "advice.rest.few": "{n} days since your last day off",
    "advice.acwr.spike": "This week is {acwr:.1f}x your usual load - a spike that size is the classic injury setup",
    "advice.acwr.high": "This week is running {acwr:.1f}x your usual load",
    "advice.acwr.low": "Load has dropped to {acwr:.1f}x your usual - you can afford more",
    "advice.monotony": "Every day has looked the same this week (monotony {monotony:.1f}) - hard days need easy days around them",
    "advice.ready.poor": "Readiness {score}/100 from this morning's check-in",
    "advice.ready.low": "Readiness {score}/100",
    "advice.ready.mid": "Readiness {score}/100",
    "advice.ready.good": "Readiness {score}/100 and nothing left to recover from",
    "advice.form.hole": "Form is {tsb:+d} - you are deep in the hole",
    "advice.form.low": "Form is {tsb:+d}",
    "advice.form.fresh": "Form is {tsb:+d} - you are fresh",
    "advice.nothing": "Nothing in your load or check-ins says to change anything",
    # what the verdict does to the session
    "session.rest.had": "Rest day. {why}. The plan had {planned} today - move it to tomorrow, the week will absorb it.",
    "session.rest.empty": "Rest day. {why}. Nothing was planned anyway.",
    "session.easy": "Easy only today. {why}. Keep it Z1-Z2 ({lo:.0f}-{hi:.0f} bpm), no intervals, and cut it "
    "short if it still feels like work. Originally planned: {was}",
    "session.moderate": "Hold it at tempo or below. {why}. Drop any reps above threshold and keep the rest of "
    "the session as written. Originally planned: {was}",
    # where the training is going
    "status.none": "Log a couple of weeks of training and this starts reading your direction.",
    "status.detraining": "Fitness is falling {drop:.1f} a week. If this is not a planned break, get a regular week back in.",
    "status.overreach.load": "Load has spiked well above what you are used to.",
    "status.overreach.form": "Form at {tsb:+d} is far enough down that fitness stops being the thing that improves.",
    "status.peaking": "Fitness is high and you are coming fresh. This is the shape you want on race day.",
    "status.productive": "Fitness is climbing {ramp:.1f} a week and you are absorbing it. Keep doing what you are doing.",
    "status.unproductive": "Load is going up but your pace at a given heart rate is drifting the wrong way. "
    "Usually sleep, stress or fuel.",
    "status.recovery": "A lighter week than usual, and form is coming back. This is where the work lands.",
    "status.maintaining": "Fitness is holding steady. Enough to keep what you have, not enough to build.",
    # how the last four weeks were spent
    "mix.polarised": "Close to the 80/20 shape most endurance training works best in.",
    "mix.grey": "{moderate}% of your time sits in the moderate band - hard enough to tire you, easy "
    "enough not to drive much adaptation. Push the hard days harder and let the easy days "
    "be genuinely easy.",
    "mix.too_easy": "Almost all of it is easy. That builds a base, but you need some genuinely hard work to get faster.",
    "mix.too_hard": "{hard}% hard is a lot. Most of it should be easy enough to hold a conversation.",
    # bests
    "pr.unclaimed": "Race or log a {label} to claim this rank",
    "pr.unclaimed.multi": "{label}: log a finish time to claim this rank",
    "pr.near": "Your {logged} on {date} is close, but too far off {target} to count. Edit it to the "
    "real distance if that is what it was.",
    "pr.source.logged": "Logged session",
    "pr.source.adjusted": "Logged as {logged}, adjusted",
    "pr.source.block": "Best block of a longer session",
    "pr.source.pace": "Average pace of a {dist} session",
    "pr.source.profile": "Profile benchmark race",
    "pr.trend.none": "Not enough dated history here yet to project a trend",
    "pr.trend.flat": "Your times here aren't trending down, so there's no honest rate to project from",
    "pr.trend.eta": "At your current rate of improvement, around {date}",
    "pr.trend.arrived": "Your recent trend already clears it - log one more effort to confirm",
}

HARD_IF = 0.82  # at or above this a session is "hard" - tempo and up

# verdict -> (label, how much of the planned session survives, what it turns into)
VERDICTS = {
    "rest": ("Take the day off", 0.0, "rest"),
    "easy": ("Keep it easy", 0.65, "easy"),
    "moderate": ("Train, but cap the intensity", 0.9, "moderate"),
    "normal": ("Go as planned", 1.0, "normal"),
    "push": ("You have room to push", 1.0, "push"),
}

# Where the training is actually going. One label, the way a watch gives you one, but with the reasoning shown.
STATUS_COLOUR = {
    "Peaking": "#b45bff",
    "Productive": "#12b76a",
    "Maintaining": "#00a3ff",
    "Recovery": "#0fb5ae",
    "Overreaching": "#e07800",
    "Unproductive": "#f0387c",
    "Detraining": "#8a919c",
    "No data": "#8a919c",
}

DEFAULT_HABITS = [
    ("h-bed", "In bed by bedtime"),
    ("h-stretch", "10 min stretching or mobility"),
    ("h-water", "Drink 8 glasses of water"),
]

DEFAULT_QUOTES = [
    ("Let it offend you that someone could be handed your days and turn them into something great.", "Seneca"),
    ("We are what we repeatedly do. Excellence, then, is not an act, but a habit.", "Will Durant"),
    ("I am not what happened to me, I am what I choose to become.", "Carl Jung"),
    ("Whether you think you can or you think you can't, you're right.", "Henry Ford"),
    ("Discipline is choosing between what you want now and what you want most.", "Abraham Lincoln"),
    ("You don't have to be great to start, but you have to start to be great.", "Zig Ziglar"),
    ("Fall seven times, stand up eight.", "Japanese proverb"),
    ("You have power over your mind, not outside events. Realize this, and you will find strength.", "Marcus Aurelius"),
    ("Suffer the pain of discipline or suffer the pain of regret.", "Jim Rohn"),
    ("Pain is temporary. Quitting lasts forever.", "Lance Armstrong"),
    ("The miracle isn't that I finished. The miracle is that I had the courage to start.", "John Bingham"),
    ("No man is free who is not master of himself.", "Epictetus"),
    ("The greater the difficulty, the more glory in surmounting it.", "Epictetus"),
    ("You have to be able to feel comfortable being uncomfortable.", "Georges St-Pierre"),
    ("You can't cross the sea merely by standing and staring at the water.", "Rabindranath Tagore"),
    ("Nobody cares about your excuses. Nobody feels sorry for you. And nobody's going to do it for you.", "Unknown"),
    ("The obstacle in the path becomes the path.", "Marcus Aurelius"),
    ("There is no elevator to success; you have to take the stairs.", "Zig Ziglar"),
    (
        "The only thing standing between you and your goal is the story you keep telling yourself about why you can't achieve it.",
        "Jordan Belfort",
    ),
    ("Your brain will always quit before your legs do.", "Unknown"),
    (
        "The wall is a myth. There's no such thing as hitting the wall. It's just a matter of how hard you're willing to push.",
        "Unknown",
    ),
    ("You don't finish a marathon because you're strong. You finish because you refuse to stop.", "Unknown"),
]

# later additions ship as their own batch, so existing databases get them once too
QUOTE_BATCHES = [
    (
        "seeded_quotes2",
        [
            ("We suffer more often in imagination than in reality.", "Seneca"),
            ("Difficulties strengthen the mind, as labor does the body.", "Seneca"),
            ("Rule your mind or it will rule you.", "Horace"),
            (
                "Man cannot remake himself without suffering, for he is both the marble and the sculptor.",
                "Alexis Carrel",
            ),
            ("It is not the mountain we conquer, but ourselves.", "Edmund Hillary"),
            ("Do not pray for an easy life, pray for the strength to endure a difficult one.", "Bruce Lee"),
            (
                "If you want to run, run a mile. If you want to experience a different life, run a marathon.",
                "Emil Zátopek",
            ),
        ],
    ),
    (
        "seeded_quotes3",
        [
            ("Somebody may beat me, but they are going to have to bleed to do it.", "Steve Prefontaine"),
            (
                "The man who can drive himself further once the effort gets painful is the man who will win.",
                "Roger Bannister",
            ),
            ("Don't wish it were easier; wish you were better.", "Jim Rohn"),
            ("Don't stop when you're tired. Stop when you're done.", "David Goggins"),
        ],
    ),
]

ACTIVITY = {"sedentary": 1.25, "light": 1.35, "moderate": 1.5, "active": 1.7}

# key -> (label, kind, help). kind: str/int/float/date/time/pace/swim/weight/height/dist/vol/bool/sports/
# or ("select", [(value, label), ...])
PROFILE_META = {
    "name": ("Name", "str", ""),
    "units": ("Units", ("select", [("imperial", "Imperial"), ("metric", "Metric")]), ""),
    "sex": ("Sex", ("select", [("M", "Male"), ("F", "Female")]), "Used for BMR"),
    "age": ("Age", "int", ""),
    "weight_kg": ("Weight", "weight", ""),
    "height_cm": ("Height", "height", ""),
    "sports": ("Your disciplines", "sports", "Shapes the log, zones, tests and plan when you have no race"),
    "ftp": ("FTP", "float", "W · 95% of a 20-min all-out"),
    "lthr": ("Lactate threshold HR", "float", "bpm · unknown? ~89% of max HR"),
    "max_hr": ("Max HR", "float", "bpm"),
    "rest_hr": ("Resting HR", "float", "bpm"),
    "hr_model": (
        "Heart-rate zone model",
        (
            "select",
            [("lthr", "Lactate threshold (Friel)"), ("max", "% of max HR"), ("hrr", "Heart-rate reserve (Karvonen)")],
        ),
        "",
    ),
    "run_thr_pace": ("Run threshold pace", "pace", "Pace you could hold ~1 hour (m:ss)"),
    "css": ("Swim CSS pace", "swim", "Critical swim speed (m:ss)"),
    "recent_race_km": ("Recent run race distance", "dist", "0 = none; anchors run predictions"),
    "recent_race_s": ("Recent run race time", "time", "h:mm:ss"),
    "cda": ("Bike CdA", "float", "m² · 0.25 aero bars – 0.35 hoods"),
    "bike_kg": ("Bike + kit weight", "weight", ""),
    "plan_start": ("Plan start", "date", ""),
    "weekly_hours": ("Current weekly hours", "float", "h"),
    "peak_hours": ("Peak weekly hours", "float", "h"),
    "days_per_week": ("Training days per week", ("select", [(n, str(n)) for n in range(3, 8)]), ""),
    "long_day": ("Long-session day", ("select", list(enumerate(DOW))), ""),
    "recovery_every": ("Recovery week", ("select", [(3, "Every 3rd week"), (4, "Every 4th week"), (0, "None")]), ""),
    "taper_weeks": (
        "Taper length",
        ("select", [(0, "Auto (by race length)"), (1, "1 week"), (2, "2 weeks"), (3, "3 weeks")]),
        "",
    ),
    "strength": ("Include strength sessions", "bool", ""),
    "plan_race": ("Plan builds to", ("select", []), "Auto = next A race, else next race"),
    "goal": ("Body-comp goal", ("select", [("maintain", "Maintain"), ("lose", "Lose weight"), ("gain", "Gain")]), ""),
    "activity": (
        "Activity outside training",
        (
            "select",
            [
                ("sedentary", "Sedentary"),
                ("light", "Light (desk + walking)"),
                ("moderate", "Moderate (on feet)"),
                ("active", "Very active job"),
            ],
        ),
        "",
    ),
    "protein_gkg": ("Protein target", "float", "g/kg · 0 = auto (1.8, or 2.2 when losing)"),
    "gut_carbs": ("Trained gut carbs", "float", "g/h you can tolerate"),
    "gel_carbs": ("Carbs per gel", "float", "g · for gel counts"),
    "sweat_rate": ("Sweat rate", "vol", "per hour · use the sweat test"),
    "sweat_na": ("Sweat sodium", "float", "mg/L · typical 400–1500"),
    "caffeine_mg": ("Habitual daily caffeine", "float", "mg · a coffee is ~95 mg, an energy drink ~80 mg"),
    "caffeine_sensitivity": (
        "Caffeine sensitivity",
        ("select", [("low", "Low (well tolerated)"), ("normal", "Normal"), ("high", "High (gets jittery easily)")]),
        "Sets where in the 3–6 mg/kg range race-day dosing sits",
    ),
    "theme": ("Theme", ("select", [("system", "Match Windows"), ("light", "Light"), ("dark", "Dark")]), ""),
    "team_on": (
        "I train with a team or coach",
        "bool",
        "Practice days show your coach's session instead of the plan's",
    ),
    "team_days": ("Practice days", "weekdays", ""),
    "team_min": ("Typical practice length", "float", "minutes"),
    "team_label": ("What to call it", "str", "e.g. XC practice"),
    "team_sport": ("Practice sport", ("select", [(x, x) for x in LEG_SPORTS]), ""),
    "team_time": ("Practice start time", "clock", "For the weather on practice days"),
    "train_time": (
        "Usual training time",
        "clock",
        "For the weather on planned sessions and logged workouts without a start time",
    ),
    "wake_weekday": ("Wake-up on school/work days", "clock", "Bedtime counts back from this"),
    "wake_weekend": ("Wake-up on other days", "clock", ""),
    "school_days": ("School/work days", "weekdays", ""),
    "sleep_goal": ("Sleep goal", "float", "hours · 0 = auto (9 for teens, 8 for adults)"),
    "winddown": ("Wind-down reminder", "int", "minutes before bedtime"),
    "notify_bedtime": ("Bedtime reminder", "bool", ""),
    "notify_checkin": ("Morning check-in reminder", "bool", ""),
    "checkin_time": ("Check-in reminder time", "clock", ""),
    "notify_nudge": ("Evening nudge if things aren't done", "bool", "With one of your quotes"),
    "nudge_time": ("Nudge time", "clock", ""),
    "brief_min": (
        "Briefing before a scheduled session",
        "int",
        "minutes before you start · weather, what to wear, what to bring · 0 = off",
    ),
}

PROFILE_SECTIONS = [
    ("Athlete", ["name", "units", "sex", "age", "weight_kg", "height_cm", "sports"]),
    (
        "Thresholds & zones",
        ["ftp", "lthr", "max_hr", "rest_hr", "hr_model", "run_thr_pace", "css", "recent_race_km", "recent_race_s"],
    ),
    (
        "Training plan",
        [
            "plan_race",
            "plan_start",
            "weekly_hours",
            "peak_hours",
            "days_per_week",
            "long_day",
            "recovery_every",
            "taper_weeks",
            "strength",
            "train_time",
        ],
    ),
    ("Team or coach", ["team_on", "team_days", "team_min", "team_label", "team_sport", "team_time"]),
    (
        "Nutrition & hydration",
        [
            "goal",
            "activity",
            "protein_gkg",
            "gut_carbs",
            "gel_carbs",
            "sweat_rate",
            "sweat_na",
            "caffeine_mg",
            "caffeine_sensitivity",
        ],
    ),
    ("Bike equipment", ["cda", "bike_kg"]),
    ("Appearance", ["theme"]),
]

CHECK_ITEMS = {
    "Swim": ["Wetsuit / swimskin", "Goggles x2 (clear + tinted)", "Swim cap", "Anti-chafe"],
    "Bike": [
        "Helmet",
        "Bike shoes",
        "Sunglasses",
        "Bottles filled",
        "Spare tube + CO2 + levers",
        "Bike checked, tyres pumped",
    ],
    "Run": ["Run shoes", "Visor / cap", "Socks", "Gels / flask"],
    "Row": ["Boat / erg settings checked"],
    "Ski": ["Skis waxed", "Poles", "Layers for conditions"],
    "Hike": ["Poles", "Headlamp", "Layers"],
    "Paddle": ["PFD", "Paddle", "Spray skirt"],
    "General": [
        "Race number + timing chip",
        "ID + phone",
        "Race nutrition packed",
        "Sunscreen / weather kit",
        "Breakfast prepped",
        "Alarm x2",
    ],
}

LEVELS = {  # rough starting points when the athlete doesn't know a number; field tests refine them
    "new": dict(
        label="New to endurance sport", sub="Under a year of regular training", wkg=2.0, thr=405, css=150, hours=(4, 7)
    ),
    "recreational": dict(
        label="Recreational", sub="Train most weeks, finish races comfortably", wkg=2.6, thr=330, css=125, hours=(6, 10)
    ),
    "experienced": dict(
        label="Experienced", sub="Structured training, several seasons", wkg=3.2, thr=285, css=105, hours=(8, 13)
    ),
    "competitive": dict(
        label="Competitive", sub="Age-group podiums or better", wkg=3.9, thr=250, css=90, hours=(11, 16)
    ),
}

P = dict(DEFAULTS)  # active profile, metric internally

# ---------------------------------------------------------------- units & formatting


def imp():
    return P.get("units") == "imperial"


def num(v):
    return f"{v:.2f}".rstrip("0").rstrip(".")


def hms(sec):
    sec = int(round(sec or 0))
    h, r = divmod(sec, 3600)
    m, s = divmod(r, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def parse_clock(s):
    t = 0.0
    for part in str(s).strip().split(":"):
        t = t * 60 + float(part or 0)
    return t


def parse_dur(s):
    """'1:30:00' / '45:00' clock, or a bare number = minutes."""
    s = str(s).strip()
    return parse_clock(s) if ":" in s else float(s or 0) * 60


def to_ui(kind, v):
    i = imp()
    if kind == "vol" and i:
        return f"{v * L_OZ:.0f}"
    if kind in LIN:
        v = v * LIN[kind][0] if i else v
        return num(v) if kind == "dist" else f"{v:.1f}".rstrip("0").rstrip(".")
    if kind == "temp":
        return f"{v * 9 / 5 + 32 if i else v:.0f}"
    if kind == "pace":
        return hms(v * KM_MI if i else v)
    if kind == "swim":
        return hms(v * YD if i else v)
    if kind == "time":
        return hms(v)
    if kind in ("float", "int"):
        return num(float(v))
    return str(v)


def from_ui(kind, s):
    s = str(s).strip()
    i = imp()
    if kind in LIN:
        v = float(s or 0)
        return v / LIN[kind][0] if i else v
    if kind == "temp":
        v = float(s)
        return (v - 32) * 5 / 9 if i else v
    if kind == "pace":
        v = parse_clock(s)
        return v / KM_MI if i else v
    if kind == "swim":
        v = parse_clock(s)
        return v / YD if i else v
    if kind == "time":
        return parse_dur(s)
    if kind == "int":
        return int(float(s))
    if kind == "float":
        return float(s or 0)
    if kind == "date":
        return dt.date.fromisoformat(s).isoformat()
    return s


def unit(kind):
    if kind in LIN:
        return LIN[kind][2 if imp() else 1]
    return {
        "temp": "°F" if imp() else "°C",
        "pace": "/mi" if imp() else "/km",
        "swim": "/100yd" if imp() else "/100m",
    }.get(kind, "")


def fd(kind, v):
    u = unit(kind)
    return to_ui(kind, v) + (u if kind in ("pace", "swim") else (" " + u if u else ""))


def speed_ui(kmh):
    return f"{kmh / KM_MI:.1f} mph" if imp() else f"{kmh:.1f} km/h"


def swim_dist_ui(km):
    return f"{km * 1000 / YD:.0f} yd" if imp() else f"{km * 1000:.0f} m"


def leg_dist_ui(sport, km):
    """Editable number: swims in m/yd, everything else km/mi."""
    return num(km * 1000 / (YD if imp() else 1)) if sport == "Swim" else num(km / KM_MI if imp() else km)


def leg_dist_from(sport, s):
    v = float(s or 0)
    return v * (YD if imp() else 1) / 1000 if sport == "Swim" else (v * KM_MI if imp() else v)


def leg_label(sport, km):
    return swim_dist_ui(km) if sport == "Swim" else fd("dist", km)


# ---------------------------------------------------------------- training science


def rpe_if(rpe):
    return 0.45 + 0.055 * max(1.0, min(10.0, rpe or 5))


def estimate_tss(p, sport, dur_s, dist_km=0, rpe=None, avg_hr=None, avg_w=None):
    """Power > pace > HR > RPE, the usual TrainingPeaks-style hierarchy."""
    h = (dur_s or 0) / 3600
    if h <= 0:
        return 0.0
    IF = None
    if sport in ("Bike", "Brick") and avg_w and p["ftp"]:
        IF = avg_w / p["ftp"]
    elif sport == "Run" and dist_km and p["run_thr_pace"]:
        IF = p["run_thr_pace"] / (dur_s / dist_km)
    elif sport == "Swim" and dist_km and p["css"]:
        ratio = p["css"] / (dur_s / (dist_km * 10))
        return round(h * min(ratio, 1.2) ** 3 * 100, 1)
    if IF is None and avg_hr and p["lthr"]:
        IF = avg_hr / p["lthr"]  # ponytail: linear hrTSS approximation, TRIMP if HR streams get imported
    if IF is None:
        IF = rpe_if(rpe)
    tss = h * min(IF, 1.2) ** 2 * 100
    return round(tss * (0.5 if sport in ("Strength", "Mobility") else 1), 1)


def estimate_kcal(p, sport, dur_s, dist_km=0, avg_w=None, tss=0):
    h = (dur_s or 0) / 3600
    if h <= 0:
        return 0.0
    if sport == "Bike" and avg_w:
        return round(avg_w * dur_s / 1000)  # kJ of work ~ kcal burned at ~24% efficiency
    if sport == "Run" and dist_km:
        return round(1.0 * p["weight_kg"] * dist_km)
    IF = math.sqrt(tss / (h * 100)) if tss else 0.7
    return round(MET.get(sport, 6) * (IF / 0.72) * p["weight_kg"] * h)


def pmc(daily, start, end, ctl=0.0, atl=0.0):
    """Performance Management Chart: CTL (42d), ATL (7d), TSB = CTL - ATL."""
    out, d = [], start
    while d <= end:
        t = daily.get(d, 0.0)
        ctl += (t - ctl) / 42
        atl += (t - atl) / 7
        out.append((d, ctl, atl, ctl - atl))
        d += ONE
    return out


def form_label(tsb):
    if tsb > 25:
        return "Very fresh - fitness fading if this lasts"
    if tsb > 5:
        return "Fresh - race ready"
    if tsb > -10:
        return "Neutral - maintaining"
    if tsb > -30:
        return "Productive training load"
    return "Overreaching risk - back off"


def bike_speed(watts, mass, cda, crr=0.004, rho=1.2, eff=0.975):
    """Flat-road steady-state speed (m/s): eff*P = Crr*m*g*v + 0.5*rho*CdA*v^3."""
    lo, hi = 0.1, 30.0
    for _ in range(60):
        v = (lo + hi) / 2
        if crr * mass * 9.81 * v + 0.5 * rho * cda * v**3 > eff * watts:
            hi = v
        else:
            lo = v
    return lo


def riegel(d1, t1, d2, k=1.06):
    t = t1 * (d2 / d1) ** k
    if d2 > 42.195:  # ponytail: Riegel is optimistic past the marathon; mild extra decay until an ultra model is needed
        t *= (d2 / 42.195) ** 0.08
    return t


_RUN_ANCHORS = []  # (km, secs): the best logged run at each standard distance in the last year


def best_run_anchors(found):
    """The fastest dated run effort per standard distance within a year. Older ones say little about today, and the
    profile's benchmark race (undated) is only a fallback for someone with nothing recent logged."""
    cutoff = (dt.date.today() - dt.timedelta(days=365)).isoformat()
    out = []
    for sport, key, _, km in RECORD_EVENTS:
        recent = [secs for secs, date, _ in found.get((sport, key), []) if date and date >= cutoff]
        if sport == "Run" and recent:
            out.append((km, min(recent)))
    return out


def run_anchor(p, km=None):
    """The (distance, time) a run prediction is scaled from: your best recent effort nearest the distance asked
    for, else the profile's recent race, else threshold pace as a one-hour effort."""
    if _RUN_ANCHORS and not p.get("_no_anchor"):
        return min(_RUN_ANCHORS, key=lambda a: (abs(math.log((km or 10.0) / a[0])), a[1]))
    if p["recent_race_km"] > 0 and p["recent_race_s"] > 0:
        return p["recent_race_km"], p["recent_race_s"]
    return 3600 / p["run_thr_pace"], 3600.0  # threshold pace ~ 1 h race pace


def predict(p, race, ctl):
    """Leg-by-leg prediction for any race. Returns segments (legs + transitions) and a total, or total=None
    if a leg can't be modelled and the race has no goal time."""
    legs = race["legs"]
    fit = max(-0.04, min(0.03, (ctl - 55) * 0.0012))  # fitter athletes hold a higher IF and fade less
    # ponytail: ~2% slower per 5°C above 15°C (half on the bike); swap for a WBGT model if racing in real heat
    heat = max(0.0, race.get("temp_c", 18) - 15) / 5 * 0.02
    if race.get("dew_c") is not None:  # forecast: humidity matters as much as temperature
        heat = heat_slowdown(race["temp_c"], race["dew_c"])[0] / 100
    mass = p["weight_kg"] + p["bike_kg"]
    segs, elapsed, modelled = [], 0.0, True
    for i, leg in enumerate(legs):
        sport, km, elev = leg["sport"], leg["km"], leg.get("elev", 0.0)
        seg = dict(kind="leg", sport=sport, km=km, elev=elev, secs=None, pace="", detail="", IF=None)
        if sport == "Swim":
            pace = p["css"] + (2 if km <= 1 else 4 if km <= 2.5 else 7)  # longer swims drift further off CSS
            seg.update(secs=km * 10 * pace, pace=fd("swim", pace), pace_s=pace)
        elif sport == "Bike":
            run_after = any(l["sport"] == "Run" for l in legs[i + 1 :])
            h = km / 30
            for _ in range(4):  # IF depends on duration, duration on IF
                IF = min(1.05, h**-0.16) * (0.92 if run_after else 1) + fit  # ~1.0 @1h, 0.84 @3h, 0.77 @5h
                watts = p["ftp"] * IF
                # ponytail: flat physics + ~15% of climbing potential energy lost (~1.3 min/100 m); GPX sim would be exact
                secs = (km * 1000 / bike_speed(watts, mass, p["cda"]) + mass * 9.81 * elev * 0.15 / watts) * (
                    1 + heat / 2
                )
                h = secs / 3600
            seg.update(secs=secs, IF=round(IF, 2), watts=watts, pace=f"{speed_ui(km / h)} · {watts:.0f} W")
        elif sport == "Run":
            d1, t1 = run_anchor(p, km)
            fresh = riegel(d1, t1, km)
            prior_h = elapsed / 3600
            fade = 1 + (0.03 + 0.018 * prior_h if i else 0) - (fit if i else fit / 2)
            secs = fresh * fade * (1 + heat) + elev * 0.6  # ~1 min per 100 m of climbing
            seg.update(secs=secs, fresh=fresh, pace=fd("pace", secs / km), pace_s=secs / km)
        else:
            modelled = False
        segs.append(seg)
        if seg["secs"]:
            elapsed += seg["secs"]
        if i < len(legs) - 1:
            t = race.get("t1", 180) if i == 0 else race.get("t2", 120)
            segs.append(dict(kind="trans", sport="T1" if i == 0 else f"T{i + 1}", secs=t))
            elapsed += t
    total = elapsed if modelled else (race.get("goal_s") or None)
    return dict(
        segs=segs,
        total=total,
        modelled=modelled,
        lo=total * 0.96 if total else None,
        hi=total * 1.05 if total else None,
    )


def hr_zones(p):
    m = p.get("hr_model", "lthr")
    if m == "lthr":
        z = [
            ("Z1 Recovery", 0, 0.85),
            ("Z2 Aerobic", 0.85, 0.89),
            ("Z3 Tempo", 0.90, 0.94),
            ("Z4 Sub-threshold", 0.95, 0.99),
            ("Z5a Threshold", 1.0, 1.02),
            ("Z5b VO2", 1.03, 1.06),
        ]
        return [(n, p["lthr"] * a, p["lthr"] * b) for n, a, b in z]
    z = [
        ("Z1 Recovery", 0.5, 0.6),
        ("Z2 Aerobic", 0.6, 0.7),
        ("Z3 Tempo", 0.7, 0.8),
        ("Z4 Threshold", 0.8, 0.9),
        ("Z5 VO2max", 0.9, 1.0),
    ]
    if m == "max":
        return [(n, p["max_hr"] * a, p["max_hr"] * b) for n, a, b in z]
    rr = p["max_hr"] - p["rest_hr"]  # Karvonen / heart-rate reserve
    return [(n, p["rest_hr"] + rr * a, p["rest_hr"] + rr * b) for n, a, b in z]


def zones(p):
    ftp, lthr, tp, css = p["ftp"], p["lthr"], p["run_thr_pace"], p["css"]
    sports = set(p["sports"])
    r = lambda z, f: [dict(name=n, range=f(a, b)) for n, a, b in z]
    groups = []
    if "Bike" in sports:
        power = [
            ("Z1 Active recovery", 0, 0.55),
            ("Z2 Endurance", 0.56, 0.75),
            ("Z3 Tempo", 0.76, 0.90),
            ("Z4 Threshold", 0.91, 1.05),
            ("Z5 VO2max", 1.06, 1.20),
            ("Z6 Anaerobic", 1.21, 1.50),
        ]
        groups.append(
            dict(
                title="Bike power",
                sub=f"FTP {ftp:.0f} W · Coggan",
                zones=r(power, lambda a, b: f"{ftp * a:.0f} – {ftp * b:.0f} W"),
            )
        )
    hz = hr_zones(p)
    model = {
        "lthr": f"LTHR {lthr:.0f} bpm · Friel",
        "max": f"Max HR {p['max_hr']:.0f} · % of max",
        "hrr": f"HR reserve {p['rest_hr']:.0f}–{p['max_hr']:.0f} · Karvonen",
    }[p.get("hr_model", "lthr")]
    if p.get("hr_model", "lthr") == "lthr" and "Bike" in sports:
        hb = [
            ("Z1 Recovery", 0, 0.81),
            ("Z2 Aerobic", 0.81, 0.89),
            ("Z3 Tempo", 0.90, 0.93),
            ("Z4 Sub-threshold", 0.94, 0.99),
            ("Z5a Threshold", 1.0, 1.02),
            ("Z5b VO2", 1.03, 1.06),
        ]
        groups.append(
            dict(title="Bike heart rate", sub=model, zones=r(hb, lambda a, b: f"{lthr * a:.0f} – {lthr * b:.0f} bpm"))
        )
        title = "Run heart rate" if "Run" in sports else "Heart rate"
    else:
        title = "Heart rate · all sports"
    groups.append(dict(title=title, sub=model, zones=[dict(name=n, range=f"{a:.0f} – {b:.0f} bpm") for n, a, b in hz]))
    if "Run" in sports:
        pace = [
            ("Z1 Recovery", 1.29, 1.45),
            ("Z2 Aerobic", 1.14, 1.29),
            ("Z3 Tempo", 1.06, 1.13),
            ("Z4 Threshold", 0.99, 1.05),
            ("Z5 VO2", 0.90, 0.98),
        ]
        groups.append(
            dict(
                title="Run pace",
                sub=f"Threshold {fd('pace', tp)} · Friel",
                zones=r(pace, lambda a, b: f"{fd('pace', tp * b)} – {fd('pace', tp * a)}"),
            )
        )
    if "Swim" in sports:
        swim = [
            ("Easy / warm-up", 10, 20),
            ("Endurance (CSS+5-10s)", 5, 10),
            ("Threshold (CSS±2s)", -2, 2),
            ("Fast (CSS-3-6s)", -6, -3),
        ]
        groups.append(
            dict(
                title="Swim pace",
                sub=f"CSS {fd('swim', css)}",
                zones=r(swim, lambda a, b: f"{fd('swim', css + a)} – {fd('swim', css + b)}"),
            )
        )
    return groups


# ---------------------------------------------------------------- records & ranks
# Every best effort lands on one 0-100 score: the share of a world-class reference performance the athlete
# reached, after an age factor. For running that number *is* the standard WMA age-grade percentage, so the tier
# bands below are its published interpretation (90 = world class, 80 = national, 70 = regional, 60 = local) and
# bike and swim are mapped onto the same scale through their own reference ladders. One tier means one thing.


def interp(table, x):
    """Linear interpolation through (x, y) anchors, extrapolating along the end segments."""
    if x <= table[0][0]:
        (x1, y1), (x2, y2) = table[0], table[1]
    elif x >= table[-1][0]:
        (x1, y1), (x2, y2) = table[-2], table[-1]
    else:
        i = max(i for i, (a, _) in enumerate(table) if a <= x)
        (x1, y1), (x2, y2) = table[i], table[i + 1]
    return y1 + (y2 - y1) * (x - x1) / (x2 - x1)


def age_factor(age):
    return interp(AGE_CURVE, max(8.0, min(100.0, float(age or 30))))


def ref_for(p, key):
    """The reference performance for this athlete's sex; `key` is a REF_TIMES / REF_THRESHOLD key."""
    pair = REF_TIMES.get(key) or REF_THRESHOLD[key]
    return pair[1] if str(p.get("sex", "M")).upper().startswith("F") else pair[0]


def tier_of(score):
    """Tier, division and progress to the next tier for a 0-100 score."""
    for i, (name, lo, hi, label, colour) in enumerate(TIERS):
        if hi is None or score < hi:
            frac = 1.0 if hi is None else max(0.0, min(1.0, (score - lo) / (hi - lo)))
            nxt = TIERS[i + 1] if i + 1 < len(TIERS) else None
            return dict(
                tier=name,
                div="" if hi is None else ["III", "II", "I"][min(2, int(frac * 3))],
                cls=label,
                colour=colour,
                score=round(score, 1),
                pct=round(frac * 100),
                next=nxt[0] if nxt else "",
                next_at=nxt[1] if nxt else None,
                next_colour=nxt[4] if nxt else "",
            )


def grade_time(p, key, secs):
    """Score a time against its reference, age-adjusted."""
    return ref_for(p, key) / max(1.0, secs * age_factor(p.get("age", 30))) * 100


def time_for_score(p, key, score):
    """The inverse: what time scores exactly `score` for this athlete. Used for 'x to the next rank'."""
    return ref_for(p, key) / (score / 100) / age_factor(p.get("age", 30))


def grade_wkg(p, wkg):
    """Score W/kg at FTP on the Coggan ladder, age-adjusted the same way a time is."""
    table = COGGAN["F" if str(p.get("sex", "M")).upper().startswith("F") else "M"]
    return interp(table, max(0.0, wkg) / age_factor(p.get("age", 30)))


def coggan_label(score):
    """The power-profile row this score sits in, floored so the category and the tier band always agree."""
    return max((x for x in COGGAN_LABEL if x[0] <= score), default=COGGAN_LABEL[0])[1]


def ftp_equivalent(watts, dur_s):
    """An effort's power scaled to what it implies for a one-hour (FTP) effort, using the plan's own IF curve."""
    return watts / min(1.05, max(0.25, (max(dur_s, 300) / 3600) ** -0.16))


def _best_window(splits, km):
    """Fastest contiguous block of splits covering `km`, scaled to exactly `km`. None if no block fits.

    Splits are one km or one mile each, so a block rarely lands on the target exactly; the leftover is removed at
    the block's own pace. That understates the athlete a little - a true max effort over the shorter distance
    would be faster - and blocks overshooting by more than WINDOW_SLACK are dropped rather than stretched, which
    is why mile splits never yield a 5K and km splits never yield a mile.
    """
    best = None
    for i in range(len(splits)):
        d = t = 0.0
        for j in range(i, len(splits)):
            d += (splits[j].get("dist_m") or 0) / 1000
            t += splits[j].get("dur_s") or 0
            if d >= km * 0.995:
                if t > 0 and d <= km * WINDOW_SLACK:
                    cand = t * km / d
                    best = cand if best is None or cand < best else best
                break
    return best


def event_window(km, sport=None):
    """The range of logged distances that counts as a standard one, as (shortest, longest).

    A flat percentage gets this backwards. Three percent of a mile is 48 m, which no GPS watch holds - a mile
    that measured 1.04 silently stopped being a mile PR - while three percent of a marathon is 1.3 km, which is
    a different race. Measurement error is close to absolute, so the allowance is capped in metres rather than
    scaled, and it is deliberately asymmetric: running a little long and scaling the time back is conservative,
    because a true mile would have been faster still, whereas scaling a short effort up flatters it.
    """
    if sport == "Bike":  # courses are measured loosely: a "40 km" time trial is 38 to 43 on real roads
        return km * 0.95, km * 1.08
    return km * 0.98, km + min(km * 0.10, 0.6)


def counts_as(have_km, want_km, sport=None):
    lo, hi = event_window(want_km, sport)
    return lo <= have_km <= hi


def _scale(secs, have_km, want_km):
    """A time adjusted to the standard distance - left alone when the two are the same race in practice, so a
    result typed in as 21.1 km comes back as the time the athlete actually ran rather than a second under it."""
    return secs if abs(have_km - want_km) <= max(want_km * 0.005, 0.03) else secs * want_km / have_km


def _efforts(rows, races, p):
    """Every qualifying effort as {(sport, key): [(secs, date, source)]}, plus the sessions that came close
    enough to have been meant as that distance but fell outside the window, so the page can say why."""
    found, near = {}, {}
    add = lambda k, secs, date, src: found.setdefault(k, []).append((secs, date, src))
    rk, rs = p.get("recent_race_km") or 0, p.get("recent_race_s") or 0
    for sport, key, label, km in RECORD_EVENTS:
        for w in rows:
            if SPORT_FAMILY.get(w["sport"], w["sport"]) != sport or not w["dur_s"] or w["sport"] == "Brick":
                continue
            d = w["dist_km"] or 0
            splits = json.loads(w["splits"]) if w["splits"] else None
            t = None
            if splits and d >= km:
                t = _best_window(splits, km)
                if t:
                    add((sport, key), t, w["date"], say("pr.source.block"))
            if not splits and event_window(km, sport)[1] < d <= km * 3:
                # a longer run at this average pace means some stretch of it was at least that fast: a safe floor,
                # and never an overstatement, so it counts until real splits show something quicker
                add((sport, key), w["dur_s"] * km / d, w["date"], say("pr.source.pace", dist=leg_label(sport, d)))
            if d and counts_as(d, km, sport):  # logged as that distance: the clean case
                adj = _scale(w["dur_s"], d, km)
                add(
                    (sport, key),
                    adj,
                    w["date"],
                    (
                        say("pr.source.logged")
                        if adj == w["dur_s"]
                        else say("pr.source.adjusted", logged=leg_label(sport, d))
                    ),
                )
            elif d and km * 0.8 <= d <= km * 1.35:
                near.setdefault((sport, key), []).append((w["date"], d, w["dur_s"]))
        for r in races:
            legs = r["legs"]
            if r["result_s"] and len(legs) == 1 and legs[0]["sport"] == sport and counts_as(legs[0]["km"], km, sport):
                add((sport, key), _scale(r["result_s"], legs[0]["km"], km), r["date"], r["name"])
        # the profile's benchmark race is usually one of the sessions above under another name, so it only
        # fills a gap - it never adds a second entry for an event the log already covers
        if sport == "Run" and rk and rs and counts_as(rk, km) and not found.get((sport, key)):
            add((sport, key), _scale(rs, rk, km), "", say("pr.source.profile"))
    return found, {k: max(v) for k, v in near.items() if k not in found}


def _threshold_metrics(p):
    """(sport, score input, display value, detail) for each discipline's sustainable-output number."""
    out, sports = [], set(p.get("sports", []))
    if "Bike" in sports and p.get("ftp") and p.get("weight_kg"):
        wkg = p["ftp"] / p["weight_kg"]
        out.append(("Bike", wkg, f"{wkg:.2f} W/kg", f"{p['ftp']:.0f} W at {fd('weight', p['weight_kg'])}"))
    if "Run" in sports and p.get("run_thr_pace"):
        out.append(("Run", p["run_thr_pace"], fd("pace", p["run_thr_pace"]), "roughly your one-hour race pace"))
    if "Swim" in sports and p.get("css"):
        out.append(("Swim", p["css"], fd("swim", p["css"]), "the pace your CSS test puts you at"))
    return out


def milestones(rows):
    """Volume and consistency bests. Untiered on purpose: there is nothing to compare them against but yourself."""
    if not rows:
        return []
    longest = max(rows, key=lambda w: w["dur_s"] or 0)
    weeks, days = {}, set()
    for w in rows:
        d = dt.date.fromisoformat(w["date"])
        mon = d - ONE * d.weekday()
        weeks[mon] = weeks.get(mon, 0) + (w["dur_s"] or 0)
        days.add(d)
    big = max(weeks.items(), key=lambda kv: kv[1])
    streak = best = 0
    prev = None
    for d in sorted(days):
        streak = streak + 1 if prev and (d - prev).days == 1 else 1
        best, prev = max(best, streak), d
    far = max((w for w in rows if (w["dist_km"] or 0) > 0), key=lambda w: w["dist_km"], default=None)
    nice = lambda s: _nice_date(dt.date.fromisoformat(s))
    out = [
        dict(
            label="Longest session",
            value=hms(longest["dur_s"] or 0),
            sub=f"{longest['sport']} · {nice(longest['date'])}",
        ),
        dict(label="Biggest week", value=f"{big[1] / 3600:.1f} h", sub=f"week of {_nice_date(big[0])}"),
        dict(label="Longest streak", value=f"{best} day" + ("s" if best != 1 else ""), sub="consecutive days trained"),
        (
            dict(
                label="Furthest",
                value=leg_label(far["sport"], far["dist_km"]),
                sub=f"{far['sport']} · {nice(far['date'])}",
            )
            if far
            else None
        ),
        dict(label="Sessions logged", value=str(len(rows)), sub=f"since {_nice_date(min(days))}"),
    ]
    return [x for x in out if x]


def multi_key(race):
    """Which standard multisport distance a race is. Matched on its legs, not its preset name, so a race entered
    as Custom still counts and a renamed preset does not drift out of the rankings."""
    legs = [(l["sport"], l["km"]) for l in race["legs"]]
    if len(legs) < 2:
        return None
    for key, label, preset, ref in MULTI_EVENTS:
        std = PRESETS[preset][1]
        if len(std) == len(legs) and all(s == t and abs(a - b) <= b * 0.06 for (s, a), (t, b) in zip(legs, std)):
            return key
    return None


def leg_times(race):
    """Recorded leg times, when the athlete filled them in. Stored on the leg itself, so no schema change and
    they sync like the rest of the race."""
    return [l for l in race["legs"] if (l.get("secs") or 0) > 0]


def _multi_efforts(races):
    """{key: [(secs, date, name)]} for finished multisport races, plus every run recorded off a bike."""
    multi, off = {}, {}
    for r in races:
        key = multi_key(r)
        if key and r["result_s"]:
            multi.setdefault(key, []).append((r["result_s"], r["date"], r["name"]))
        biked = False
        for leg in r["legs"]:
            if leg["sport"] == "Run" and biked and (leg.get("secs") or 0) > 0:
                km = min(REF_OFF_BIKE, key=lambda d: abs(d - leg["km"]))
                if counts_as(leg["km"], km):
                    off.setdefault(km, []).append((_scale(leg["secs"], leg["km"], km), r["date"], r["name"]))
            biked = biked or leg["sport"] == "Bike"
    return multi, off


def _steps(ref, p, sport, km):
    """Every division's entry time, best first; Iron has no floor worth quoting."""
    af = age_factor(p.get("age", 30))
    steps = []
    for name, lo, hi, _, colour in reversed(TIERS):
        if lo <= 0:
            continue
        for div, k in ([("", 0)] if hi is None else [("I", 2), ("II", 1), ("III", 0)]):
            at = lo if hi is None else lo + (hi - lo) * k / 3
            need = ref / (at / 100) / af
            steps.append(
                dict(
                    tier=name,
                    div=div,
                    colour=colour,
                    at=round(at, 1),
                    time=hms(need),
                    pace=event_pace(sport, need, km) if km else "",
                )
            )
    return steps


def _rank_trend(hits, goal_secs):
    """How this event's logged times are moving, in plain words, toward goal_secs - the next rank's time.

    Fit a line through dated efforts only (the undated profile benchmark can't anchor a rate), collapsing
    same-day entries to their best first so a single busy week doesn't out-vote months of real spread. Too
    few distinct dates, or a trend that is flat or going the wrong way, says so rather than printing a
    confident date built on noise - showing the reasoning is the point, not just the number.
    """
    if not goal_secs:
        return None
    by_date = {}
    for secs, date, _ in hits:
        if date:
            by_date[date] = min(secs, by_date.get(date, secs))
    pts = sorted(by_date.items())
    if len(pts) < 3:
        return say("pr.trend.none")
    x0 = dt.date.fromisoformat(pts[0][0]).toordinal()
    xs = [dt.date.fromisoformat(d).toordinal() - x0 for d, _ in pts]
    ys = [s for _, s in pts]
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    varx = sum((x - mx) ** 2 for x in xs)
    if varx == 0:  # every dated effort fell on the same day - no spread to fit a rate to
        return say("pr.trend.none")
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / varx
    if slope >= 0:  # times holding flat or getting slower - no rate to project forward
        return say("pr.trend.flat")
    today_x = dt.date.today().toordinal() - x0
    pred_today = my + slope * (today_x - mx)
    if pred_today <= goal_secs:
        return say("pr.trend.arrived")
    eta = dt.date.today() + dt.timedelta(days=(goal_secs - pred_today) / slope)
    year = f", {eta.year}" if (eta - dt.date.today()).days > 300 else ""  # a far-out date needs its year too
    return say("pr.trend.eta", date=f"{eta:%b} {eta.day}{year}")


def _ranked(hits, ref, p, label, **extra):
    """One ranked row from a list of (secs, date, source): the best, what it beat, and what the next tier costs.

    "Previous best" is the next best effort you have, not the one that happened to be most recent before it.
    Entering an old PR after the fact is a normal thing to do, and it should still tell you what it beat.
    """
    ranked = sorted(hits)
    secs, date, src = ranked[0]
    prev = ranked[1][0] if len(ranked) > 1 else None
    af = age_factor(p.get("age", 30))
    t = tier_of(ref / max(1.0, secs * af) * 100)
    goal = ref / (t["next_at"] / 100) / af if t["next_at"] else None
    km = extra.get("km")
    steps = _steps(ref, p, extra["sport"], km)
    return dict(
        label=label,
        have=True,
        steps=steps,
        secs=secs,
        time=hms(secs),
        date=date,
        source=src,
        count=len(hits),
        prev=hms(prev) if prev else "",
        gain=hms(prev - secs) if prev and prev > secs else "",
        to_next=hms(secs - goal) if goal and goal < secs else "",
        next_time=hms(goal) if goal else "",
        trend=_rank_trend(hits, goal),
        age_graded=af != 1.0,
        open=tier_of(round(ref / max(1.0, secs) * 100, 1)),
        **extra,
        **t,
    )


def event_pace(sport, secs, km):
    if sport == "Bike":
        return speed_ui(km / (secs / 3600))
    return (
        fd("swim", secs / (km * 10))
        if sport == "Swim"
        else fd("swim", secs / (km * 5)).replace(unit("swim"), "/500m") if sport == "Row" else fd("pace", secs / km)
    )


def _near_hint(sport, label, km, miss):
    """A session that was probably meant as this distance but measured outside the window. Saying so beats
    leaving someone to wonder why the PR they just typed in did not count."""
    date, d, dur = miss
    return say(
        "pr.near", logged=leg_label(sport, d), date=_nice_date(dt.date.fromisoformat(date)), target=leg_label(sport, km)
    )


def leg_rank(p, sport, km, secs):
    """The tier a single-leg time at any distance would earn, graded against the nearest standard event of that
    sport with its reference carried to this distance. Not meaningful for a multisport race.
    ponytail: Riegel's 1.06 carries the reference between distances; fine within a factor of a few, loose past that."""
    near = [(abs(math.log(km / ek)), sport_, key, ek) for sport_, key, _, ek in RECORD_EVENTS if sport_ == sport]
    if not near or km <= 0 or not secs:
        return None
    _, _, key, ek = min(near)
    ref = ref_for(p, (sport, key)) * (km / ek) ** 1.06
    return tier_of(ref / (secs * age_factor(p.get("age", 30))) * 100)


def log_estimate(rows, sport, km):
    """A time for a sport the model has no physics for (rowing, skiing, hiking...), scaled from your own best
    comparable effort in the log. None when there is nothing near enough to scale from."""
    best = None
    for w in rows:
        d, t = w["dist_km"] or 0, w["dur_s"] or 0
        if w["sport"] == sport and d > 0 and t > 0 and km * 0.25 <= d <= km * 4:
            est = riegel(d, t, km)
            best = est if best is None else min(best, est)
    return best


def records(rows, races, p):
    """Ranked personal bests - single sport, multisport and off the bike - the threshold ranks and milestones."""
    found, near, out = *_efforts(rows, races, p), []
    for sport, key, label, km in RECORD_EVENTS:
        hits = found.get((sport, key))
        if not hits:
            if sport in p.get("sports", []):
                miss = near.get((sport, key))
                out.append(
                    dict(
                        sport=sport,
                        key=key,
                        label=label,
                        km=km,
                        have=False,
                        score=0,
                        steps=_steps(ref_for(p, (sport, key)), p, sport, km),
                        hint=_near_hint(sport, label, km, miss) if miss else say("pr.unclaimed", label=label),
                    )
                )
            continue
        out.append(
            _ranked(
                hits,
                ref_for(p, (sport, key)),
                p,
                label,
                sport=sport,
                key=key,
                km=km,
                pace=event_pace(sport, min(hits)[0], km),
            )
        )
    multi_hits, off_hits = _multi_efforts(races)
    multi = []
    for key, label, preset, ref in MULTI_EVENTS:
        kind = race_kind(dict(legs=[dict(sport=s, km=k) for s, k in PRESETS[preset][1]]))
        if key in multi_hits:
            multi.append(
                _ranked(multi_hits[key], ref[1] if _female(p) else ref[0], p, label, sport=kind, key=key, course=True)
            )
        elif race_focus([s for s, _ in PRESETS[preset][1]]) in _my_focus(p):
            multi.append(
                dict(
                    sport=kind,
                    key=key,
                    label=label,
                    have=False,
                    score=0,
                    steps=_steps(ref[1] if _female(p) else ref[0], p, kind, None),
                    hint=say("pr.unclaimed.multi", label=label),
                )
            )
    off = [
        _ranked(
            hits,
            REF_OFF_BIKE[km][1 if _female(p) else 0],
            p,
            OFF_BIKE_LABEL[km],
            sport="Brick",
            key=f"ob{km}",
            km=km,
            pace=fd("pace", min(hits)[0] / km),
        )
        for km, hits in sorted(off_hits.items())
    ]
    thr = []
    for sport, val, shown, detail in _threshold_metrics(p):
        t = tier_of(grade_wkg(p, val) if sport == "Bike" else grade_time(p, (sport, "thr"), val))
        thr.append(
            dict(
                sport=sport, value=shown, detail=detail, coggan=coggan_label(t["score"]) if sport == "Bike" else "", **t
            )
        )
    best = {}
    for r in out + thr:
        if r.get("have", True):  # threshold rows carry no `have`: they always count
            best[r["sport"]] = max(best.get(r["sport"], 0.0), r["score"])
    mine = [s for s in ("Swim", "Bike", "Run", "Row") if s in best]
    done = [m for m in multi if m.get("have")]
    return dict(
        events=out,
        multi=multi,
        off_bike=off,
        thresholds=thr,
        milestones=milestones(rows),
        by_sport=[dict(sport=s, **tier_of(best[s])) for s in mine],
        overall=tier_of(sum(best[s] for s in mine) / len(mine)) if mine else None,
        # a multisport result measures all three at once, so it is its own headline rather than a
        # fourth discipline averaged into the overall rank
        race_rank=(
            dict(label=max(done, key=lambda m: m["score"])["label"], **tier_of(max(m["score"] for m in done)))
            if done
            else None
        ),
        bricks=brick_summary(rows),
        sex="F" if _female(p) else "M",
        age=int(p.get("age", 30) or 30),
        age_factor=round(age_factor(p.get("age", 30)), 3),
        tiers=[dict(tier=n, at=lo, cls=lab, colour=c) for n, lo, _, lab, c in TIERS],
    )


def _female(p):
    return str(p.get("sex", "M")).upper().startswith("F")


def _my_focus(p):
    """The multisport shapes this athlete's disciplines can cover, so empty ranks only show if they are reachable."""
    s = set(p.get("sports", []))
    out = {race_focus([x]) for x in s}
    for combo in (("Swim", "Bike", "Run"), ("Run", "Bike"), ("Swim", "Bike")):
        if set(combo) <= s:
            out.add(race_focus(list(combo)))
    return out


def brick_summary(rows):
    """Bricks get no rank: a bike-then-run session has no standard to measure against, and its combined distance
    is not a distance anyone races. What it does have is volume, and it is the session triathlon form comes from."""
    bricks = [w for w in rows if w["sport"] == "Brick"]
    if not bricks:
        return None
    longest = max(bricks, key=lambda w: w["dur_s"] or 0)
    recent = sum(1 for w in bricks if (dt.date.today() - dt.date.fromisoformat(w["date"])).days <= 56)
    return dict(
        count=len(bricks),
        recent=recent,
        longest=hms(longest["dur_s"] or 0),
        last=_nice_date(dt.date.fromisoformat(max(w["date"] for w in bricks))),
    )


# ---------------------------------------------------------------- races


def race_from_row(r):
    return dict(
        id=r["id"],
        uid=r["uid"],
        name=r["name"],
        date=r["date"],
        preset=r["preset"],
        legs=json.loads(r["legs"]),
        priority=r["priority"],
        temp_c=r["temp_c"],
        t1=r["t1"],
        t2=r["t2"],
        goal_s=r["goal_s"],
        result_s=r["result_s"],
        notes=r["notes"] or "",
        start=r["start"] or "08:00",
    )


def race_kind(race):
    s = {l["sport"] for l in race["legs"]}
    if len(race["legs"]) == 1:
        return race["legs"][0]["sport"]
    return (
        "Triathlon"
        if {"Swim", "Bike", "Run"} <= s
        else "Duathlon" if s == {"Run", "Bike"} else "Aquabike" if s == {"Swim", "Bike"} else "Multisport"
    )


def race_focus(sports):
    """Which plan template fits a set of disciplines."""
    s = set(sports) & set(LEG_SPORTS)
    if {"Swim", "Bike", "Run"} <= s:
        return "tri"
    if {"Bike", "Run"} <= s:
        return "du"
    if {"Swim", "Bike"} <= s:
        return "aquabike"
    for k in ("Run", "Bike", "Swim"):
        if k in s:
            return k.lower()
    return next(iter(s), "Other")


# ---------------------------------------------------------------- plan


def team_desc(p):
    label = p.get("team_label") or TEAM_TAG
    lead = TEAM_TAG if label == TEAM_TAG else f"{TEAM_TAG} ({label})"
    return (
        f"{lead}: do your coach's session, then log what it was (easy, workout, long, recovery) with how hard it felt."
    )


def is_team(sess):
    return sess[4].startswith(TEAM_TAG)


def sched_from_row(r):
    return dict(
        uid=r["uid"],
        date=r["date"],
        time=r["time"] or "07:00",
        sport=r["sport"],
        kind=r["kind"] or "Easy",
        dur_s=r["dur_s"] or 0.0,
        dist_km=r["dist_km"] or 0.0,
        notes=r["notes"] or "",
    )


def sched_pace(p, sc):
    """Target pace range (s/km, slow, fast) for a paced sport, or None."""
    if sc["sport"] not in PACED:
        return None
    slow, fast = SCHED_KINDS[sc["kind"]][1]
    m = PACED[sc["sport"]]
    return p["run_thr_pace"] * slow * m, p["run_thr_pace"] * fast * m


def sched_duration(p, sc):
    """What the athlete entered, else an estimate from the distance."""
    if sc["dur_s"]:
        return sc["dur_s"]
    km, IF = sc["dist_km"], SCHED_KINDS[sc["kind"]][0]
    if not km:
        return 0.0
    pace = sched_pace(p, sc)
    if pace:
        return km * (pace[0] + pace[1]) / 2
    if sc["sport"] == "Bike":
        return km * 1000 / bike_speed(p["ftp"] * IF, p["weight_kg"] + p["bike_kg"], p["cda"])
    if sc["sport"] == "Swim":
        return km * 10 * (p["css"] + 8)
    return 0.0


def sched_desc(p, sc):
    dur, km = sched_duration(p, sc), sc["dist_km"]
    size = " · ".join(x for x in (leg_label(sc["sport"], km) if km else "", hms(dur) if dur else "") if x)
    pace = sched_pace(p, sc)
    tgt = f" @ {fd('pace', pace[1]).split('/')[0]}-{fd('pace', pace[0])}" if pace else ""
    note = f" {sc['notes']}" if sc["notes"] else ""
    return (
        f"{sc['kind']} {sc['sport'].lower()} you scheduled for {fmt12(at(dt.date.fromisoformat(sc['date']), sc['time']))}"
        f"{': ' + size if size else ''}{tgt}. {SCHED_DETAIL[sc['kind']].capitalize()}.{note}"
    )


def wx_during(wx, start, end):
    """Summarise an Open-Meteo hourly forecast (local times) over a session. None if it doesn't cover it."""
    h = (wx or {}).get("hourly") or {}
    times = h.get("time") or []
    first = start.replace(minute=0, second=0, microsecond=0)
    idx = [i for i, t in enumerate(times) if first <= dt.datetime.fromisoformat(t) <= max(end, first)]
    if not idx:
        return None
    col = lambda k: [h[k][i] for i in idx if h.get(k) and h[k][i] is not None]
    val = lambda k, f, d=None: f(col(k)) if col(k) else d
    code = val("weather_code", max, 0)
    return dict(
        temp=val("temperature_2m", lambda v: v[0]),
        temp_max=val("temperature_2m", max),
        feels=val("apparent_temperature", min),
        feels_max=val("apparent_temperature", max),
        dew=val("dew_point_2m", max),
        rh=val("relative_humidity_2m", max),
        rain=val("precipitation_probability", max, 0),
        mm=val("precipitation", sum, 0),
        wind=val("wind_speed_10m", max, 0),
        gust=val("wind_gusts_10m", max, 0),
        uv=val("uv_index", max, 0),
        dark=0 in col("is_day"),
        code=code,
        sky=next(t for c, t in WMO if code <= c) if code <= 99 else "",
    )


def heat_slowdown(temp_c, dew_c):
    """Runner's rule of thumb: air temp + dew point (°F) -> % slower pace. Returns (pct, too_hot)."""
    tot = temp_c * 9 / 5 + 32 + dew_c * 9 / 5 + 32
    pts = [(100, 0), (110, 0.5), (120, 1.5), (130, 2.5), (140, 3.75), (150, 5.25), (160, 7), (170, 9), (180, 11)]
    if tot <= 100:
        return 0.0, False
    for (a, pa), (b, pb) in zip(pts, pts[1:]):
        if tot <= b:
            return pa + (pb - pa) * (tot - a) / (b - a), False
    return 11.0, True


def what_to_wear(sport, kind, w):
    """Clothing for the conditions. Effort warms you up, so runners dress for ~8°C warmer than it feels."""
    if sport == "Swim":
        return ["Swimsuit, cap and goggles (a spare pair)", "A warm layer for afterwards"]
    warm = {"Run": 8, "Hike": 4, "Walk": 3, "Bike": -3}.get(sport, 5) - (2 if kind == "Recovery" else 0)
    f = (w["feels"] + warm) * 9 / 5 + 32  # dress-for temperature, °F bands
    tiers = [
        (80, ["Singlet or your lightest tee", "Shorts", "Cap or visor, sunglasses"]),
        (65, ["Light tee", "Shorts"]),
        (55, ["Tee, or a light long sleeve if it's windy", "Shorts"]),
        (45, ["Long-sleeve tech top", "Shorts or light tights", "Light gloves"]),
        (35, ["Long sleeve + a light jacket or vest", "Tights", "Gloves", "Headband or beanie"]),
        (25, ["Thermal base layer + wind jacket", "Tights (thermal if windy)", "Warm gloves", "Beanie", "Neck gaiter"]),
        (-99, ["Thermal base + insulated windproof jacket", "Thermal tights", "Mittens", "Beanie and face cover"]),
    ]
    out = list(next(items for lim, items in tiers if f >= lim))
    if sport == "Bike":
        out = ["Helmet"] + out + (["Arm and knee warmers you can take off"] if 45 <= f < 65 else [])
    if WET(w["code"]) or w["rain"] >= 50:
        out.append("Cap with a brim for the rain" + (", plus a light waterproof shell" if f < 60 else ""))
        out.append("Anti-chafe: wet kit rubs")
    if w["wind"] >= 25:
        out.append("Something windproof; start into the wind so it's behind you on the way home")
    if ICY(w["code"]) or (w["temp"] <= 0 and w["mm"] > 0):
        out.append("Trail shoes or traction for ice; shorten your stride")
    if w["dark"]:
        out.append("Reflective vest and a headlamp or clip light" if sport != "Bike" else "Front and rear lights")
    elif w["uv"] >= 6:
        out.append("Sunscreen")
    if w["temp_max"] - w["temp"] >= 5:
        out.append(
            f"It warms up {fd('temp', w['temp_max']).split()[0]}° by the end: a layer you can tie around your waist"
        )
    if f < 25:
        out.append("Consider going shorter, or indoors")
    return out


def kind_of(sess):
    """Classify a plan session for the briefing, from its description and intensity."""
    h = sess[2] / 3600 if sess[2] else 0
    IF = math.sqrt(sess[3] / h / 100) if h else 0.7
    d = sess[4].lower()
    return (
        "Long"
        if d.startswith("long") or "race simulation" in d
        else (
            "Intervals"
            if IF >= 0.87
            else "Tempo" if IF >= 0.8 else "Recovery" if IF < 0.66 or d.startswith(("recovery", "easy 20")) else "Easy"
        )
    )


def session_time(p, sess):
    return p.get("team_time", "15:30") if is_team(sess) else p.get("train_time", "07:00")


def best_window(wx, day, dur_s):
    """The most comfortable daylight start (6 AM to 8 PM) for a session: cool, dry, calm, no storms."""
    best = None
    for hr in range(6, 21):
        start = dt.datetime.combine(day, dt.time(hr))
        w = wx_during(wx, start, start + dt.timedelta(seconds=max(dur_s, 1800)))
        if not w or w["dark"]:
            continue
        score = (
            (heat_slowdown(w["temp_max"], w["dew"])[0] if w["dew"] is not None else 0)
            + w["rain"] / 15
            + max(0, w["wind"] - 25) / 10
            + (10 if w["code"] >= 95 else 0)
            + max(0, 5 - w["feels"]) / 3
        )
        if not best or score < best[0]:
            best = (score, start, w)
    return best


def wx_short(w):
    return f"{fd('temp', w['temp'])}, {w['sky'].lower()}" + (f", {w['rain']:.0f}% rain" if w["rain"] >= 30 else "")


def session_brief(p, sc, wx, tsb, ready, issues):
    day = dt.date.fromisoformat(sc["date"])
    start = at(day, sc["time"])
    dur = sched_duration(p, sc)
    IF, _, zi = SCHED_KINDS[sc["kind"]]
    w = wx_during(wx, start, start + dt.timedelta(seconds=dur or 3600))
    pace, hz = sched_pace(p, sc), hr_zones(p)
    adv, pct, too_hot = [], 0.0, False
    if w and w["dew"] is not None and sc["sport"] in ("Run", "Walk", "Hike", "Bike"):
        pct, too_hot = heat_slowdown(w["temp_max"], w["dew"])
    if pace and pct:
        pace = (pace[0] * (1 + pct / 100), pace[1] * (1 + pct / 100))
        dur = dur * (1 + pct / 100) if not sc["dur_s"] else dur
    if too_hot:
        adv.append("Heat and humidity are dangerous today: go very early or indoors, easy effort only.")
    elif pct >= 3:
        adv.append(f"Heat and humidity cost about {pct:.0f}% of pace: run by heart rate, not the watch.")
    if sc["kind"] in ("Tempo", "Intervals", "Race pace", "Long") and (tsb < -25 or (ready is not None and ready < 60)):
        adv.append(
            "You're carrying a lot of fatigue: "
            + (
                "cut it about 20% short and keep it Z2."
                if sc["kind"] == "Long"
                else "consider making this an easy run instead."
            )
        )
    for i in issues:
        if sc["sport"] in i["sports"] and i["kind"] in ("Injury", "Other"):
            adv.append(
                f"{i['name']} ({SEVERITY[i['severity']].lower()}): only if it's pain-free, and stop if pain goes above 3/10."
            )
        elif i["kind"] in ("Illness", "Fatigue"):
            adv.append(f"{i['name']}: keep it easy and short.")
    if w and w["gust"] >= 50:
        adv.append("Strong gusts: pick a sheltered route.")
    if w and w["code"] >= 95:
        adv.append("Thunderstorms forecast: don't be out in the open when there's lightning.")
    kg, gel = p["weight_kg"], p.get("gel_carbs") or 25
    h = dur / 3600
    hot = w and w["temp_max"] >= 24
    fluid = min(p["sweat_rate"] * (1.25 if hot else 1) * 0.75, 1.2) * h
    if w and sc["sport"] in OUTDOOR:  # a better time of day, or indoors
        b = best_window(wx, day, dur)
        mine_score = (
            pct
            + w["rain"] / 15
            + max(0, w["wind"] - 25) / 10
            + (10 if w["code"] >= 95 else 0)
            + max(0, 5 - w["feels"]) / 3
        )
        if w["code"] >= 95 or (w["rain"] >= 70 and w["mm"] >= 2):
            alt = {"Run": "treadmill", "Bike": "indoor trainer"}.get(sc["sport"], "indoor option")
            adv.append(
                f"{w['sky']} around {fmt12(start)}: take it to the {alt}"
                + (
                    f", or go at {fmt12(b[1])} ({wx_short(b[2])})."
                    if b and b[1] != start and b[0] < mine_score - 2
                    else "."
                )
            )
        elif b and b[1] != start and b[0] < mine_score - 2:
            adv.append(f"Better window: {fmt12(b[1])} ({wx_short(b[2])}) instead of {fmt12(start)} ({wx_short(w)}).")
    carbs = carbs_per_hour(p, h, sc["sport"]) * h
    bring = []
    if carbs >= 15:
        bring.append(
            f"{max(1, round(carbs / gel))} gel{'s' if round(carbs / gel) > 1 else ''} (~{carbs:.0f} g carbs, from ~30 min in)"
        )
    if h >= 1 or (hot and h >= 0.6):
        bring.append(
            f"About {fd('vol', fluid)} to drink"
            + (" (handheld or vest, or a loop past water)" if sc["sport"] in PACED else "")
        )
    if h >= 1.5 or (hot and h >= 1):
        bring.append(f"Electrolytes: ~{min(p['sweat_rate'] * 0.75, 1.0) * p['sweat_na']:.0f} mg sodium an hour")
    if sc["sport"] not in ("Swim", "Strength", "Mobility"):
        bring.append("Phone and ID")
    ready_txt = f"{form_label(tsb).split(' - ')[0]} (form {tsb:+.0f})" + (
        f", readiness {ready}/100" if ready is not None else ""
    )
    weather = None
    if w:
        weather = dict(
            sky=w["sky"],
            temp=fd("temp", w["temp"]),
            feels=fd("temp", w["feels"]),
            temp_max=fd("temp", w["temp_max"]),
            dew=fd("temp", w["dew"]) if w["dew"] is not None else "",
            rh=f"{w['rh']:.0f}%" if w["rh"] is not None else "",
            rain=f"{w['rain']:.0f}%",
            wind=(f"{w['wind'] / 1.609:.0f} mph" if imp() else f"{w['wind']:.0f} km/h"),
            uv=f"{w['uv']:.0f}",
            dark=w["dark"],
        )
    return dict(
        uid=sc["uid"],
        sport=sc["sport"],
        kind=sc["kind"],
        date=sc["date"],
        time=sc["time"],
        notes=sc["notes"],
        when=f"{day:%a, %b} {day.day} · {fmt12(start)}",
        title=f"{sc['kind']} {sc['sport'].lower()}",
        dist=leg_label(sc["sport"], sc["dist_km"]) if sc["dist_km"] else "",
        dur=hms(dur) if dur else "",
        back=fmt12(start + dt.timedelta(seconds=dur)) if dur else "",
        pace=f"{fd('pace', pace[1]).split('/')[0]}-{fd('pace', pace[0])}" if pace else "",
        heat=round(pct, 1),
        hr=f"{hz[zi][1]:.0f}-{hz[zi][2]:.0f} bpm" if zi < len(hz) else "",
        detail=SCHED_DETAIL[sc["kind"]],
        tss=round(h * IF * IF * 100),
        kcal=round(estimate_kcal(p, sc["sport"], dur, sc["dist_km"])) if dur else 0,
        ready=ready_txt,
        weather=weather,
        wear=what_to_wear(sc["sport"], sc["kind"], w) if w else [],
        bring=bring,
        fuel=fuel_session(p, sc["sport"], dur, IF, bool(hot)),
        advice=adv,
    )


def targets(p, race=None, pred=None):
    ftp, tp, css = p["ftp"], p["run_thr_pace"], p["css"]
    w = lambda a, b: f"{ftp * a:.0f}-{ftp * b:.0f} W"
    racew, race_run, has_brick = w(0.75, 0.82), fd("pace", tp * 1.1), False
    for s in (pred or {}).get("segs", []):
        if s["kind"] == "leg" and s["sport"] == "Bike" and s.get("watts"):
            racew = f"{s['watts'] - ftp * .03:.0f}-{s['watts']:.0f} W"
        if s["kind"] == "leg" and s["sport"] == "Run" and s.get("pace_s"):
            race_run = fd("pace", s["pace_s"])
    if race:
        sp = [l["sport"] for l in race["legs"]]
        has_brick = any(a == "Bike" and b == "Run" for a, b in zip(sp, sp[1:]))
    hz = hr_zones(p)
    t = dict(
        z1w=f"{ftp * .55:.0f} W",
        z2w=w(0.56, 0.75),
        tempow=w(0.76, 0.90),
        ssw=w(0.88, 0.94),
        thrw=w(0.95, 1.05),
        racew=racew,
        vo2w=w(1.06, 1.2),
        easy=f"{fd('pace', tp * 1.14)}-{fd('pace', tp * 1.29)}",
        steady=fd("pace", tp * 1.1),
        thr=fd("pace", tp),
        vo2p=fd("pace", tp * 0.94),
        race_run=race_run,
        cssp=fd("swim", css),
        css_easy=fd("swim", css + 8),
        carbs=f"{p['gut_carbs']:.0f}",
        hr2=f"{hz[1][1]:.0f}-{hz[1][2]:.0f} bpm",
        hr4=f"{hz[3][1]:.0f}-{hz[3][2]:.0f} bpm",
    )
    t["brick"] = f" Then a 15-30 min brick run @ {race_run}." if has_brick else ""
    return t


def race_tss(total_s):
    h = (total_s or 3600) / 3600
    IF = 0.95 if h < 1 else 0.85 if h < 2.5 else 0.78 if h < 5 else 0.68
    return h * IF * IF * 100


def pick_target(p, races, today):
    upcoming = [r for r in races if dt.date.fromisoformat(r["date"]) >= today]
    chosen = next((r for r in upcoming if p.get("plan_race") and r.get("uid") == p.get("plan_race")), None)
    return chosen or next((r for r in upcoming if r["priority"] == "A"), None) or (upcoming[0] if upcoming else None)


def taper_weeks(p, total_s):
    if p.get("taper_weeks"):
        return int(p["taper_weeks"])
    h = (total_s or 3600) / 3600
    return 1 if h < 1.5 else 2 if h < 5 else 3


def build_plan(p, races, today=None, ctl=50, issues=None, scheduled=None):
    """Monday-Sunday weeks from plan start through the target race week (or 12 rolling weeks with no race).
    Returns (target, [{start, phase, hours, sessions:[(date, sport, dur_s, tss, desc, race_id)]}])."""
    today = today or dt.date.today()
    target = pick_target(p, races, today)
    start = dt.date.fromisoformat(p["plan_start"])
    tpred = predict(p, target, ctl) if target else None
    tgt = targets(p, target, tpred)
    focus = race_focus([l["sport"] for l in target["legs"]] if target else p["sports"])
    main = focus if focus in TEMPLATES else "generic"
    tmpl = [(wd, k, focus if sp == "*" else sp, sh, IF, pr) for wd, k, sp, sh, IF, pr in TEMPLATES[main]]
    # rotate so the longest session lands on the athlete's chosen day
    anchor = max(wd for wd, k, *_ in tmpl if k.startswith(("long", "gen_long", "swim_long")))
    rot = (int(p.get("long_day", 6)) - anchor) % 7
    tmpl = [((wd + rot) % 7, *rest) for wd, *rest in tmpl]
    days = sorted(
        {t[0] for t in tmpl},
        key=lambda d: (min(t[5] for t in tmpl if t[0] == d), -sum(t[3] for t in tmpl if t[0] == d)),
    )
    keep = set(days[: max(1, int(p.get("days_per_week", 6)))])
    tmpl = [t for t in tmpl if t[0] in keep]
    tot = sum(t[3] for t in tmpl)
    if target:
        race_day = dt.date.fromisoformat(target["date"])
        s0 = min(start, race_day)
        week0 = s0 - ONE * s0.weekday()  # calendar weeks, Monday-Sunday; the race week is the one holding race day
        n = ((race_day - ONE * race_day.weekday()) - week0).days // 7 + 1
        T = min(taper_weeks(p, tpred["total"]), n)
    else:
        race_day, n, T = None, 12, 0
        week0 = start - ONE * start.weekday()
    R = int(p.get("recovery_every", 4))
    build_n = max(1, n - T)
    weeks = []
    for i in range(n):
        ws = week0 + dt.timedelta(weeks=i)
        out = n - i
        if target and out == 1:
            phase, hrs = "Race week", p["peak_hours"] * 0.4
        elif target and out <= T:
            phase, hrs = "Taper", p["peak_hours"] * (0.6 + 0.1 * (out - 2))
        else:
            frac = i / max(1, build_n - 1)
            hrs = p["weekly_hours"] + (p["peak_hours"] - p["weekly_hours"]) * frac
            phase = "Peak" if target and out <= T + 3 else "Build" if frac >= 0.45 else "Base"
            if R and (i + 1) % R == 0 and out > T + 1:
                phase, hrs = "Recovery", hrs * 0.65
        sessions = []
        for wd, key, sport, share, IF, _ in tmpl:
            day = ws + dt.timedelta(days=(wd - ws.weekday()) % 7)
            dur = hrs * 3600 * share / tot
            if phase == "Race week":
                d = RACE_WEEK_DESC.get(sport, RACE_WEEK_DESC["*"])
            else:
                d = DESC[key].get(phase, DESC[key].get("*", DESC[key].get("Base"))).format(sport=sport, **tgt)
            sessions.append([day, sport, dur, dur / 3600 * IF * IF * 100, d, None])
        if p.get("strength") and phase in ("Base", "Build", "Recovery", "Peak"):
            for k, off in enumerate((2, 4)[: 1 if phase in ("Peak", "Recovery") else 2]):
                day = ws + dt.timedelta(days=((int(p.get("long_day", 6)) + off) - ws.weekday()) % 7)
                sessions.append(
                    [
                        day,
                        "Strength",
                        1800,
                        20.0,
                        "Strength 30 min: squats, RDLs, split squats, calf raises, core. "
                        + ("Heavy, low reps." if phase == "Build" else "Moderate load, good form."),
                        None,
                    ]
                )
        if p.get("team_on") and p.get("team_days"):  # coach-led practice replaces the plan's own sessions on those days
            tdays = {ws + dt.timedelta(days=(int(wd) - ws.weekday()) % 7) for wd in p["team_days"]}
            sessions = [x for x in sessions if x[0] not in tdays]
            mins = float(p.get("team_min") or 90)
            for d in sorted(tdays):
                sessions.append(
                    [d, p.get("team_sport") or "Run", mins * 60, mins / 60 * 0.75**2 * 100, team_desc(p), None]
                )
        weeks.append(dict(start=ws, phase=phase, sessions=sessions, target_s=hrs * 3600))

    def on(d):
        return [s for w in weeks for s in w["sessions"] if s[0] == d]

    def drop(d, keep_team=False):
        for w in weeks:
            w["sessions"] = [s for s in w["sessions"] if s[0] != d or (keep_team and is_team(s))]

    def around_race(d, note, sport, secs, tss, desc):
        """Day before/after a race: team practice stays (with a note), otherwise the plan's own easy session."""
        drop(d, keep_team=True)
        team = [s for s in on(d) if is_team(s)]
        for s in team:
            s[4] += " " + note
        if not team:
            add(d, sport, secs, tss, desc, None)

    def add(d, *sess):
        for w in weeks:
            if w["start"] <= d < w["start"] + 7 * ONE:
                w["sessions"].append([d, *sess])

    first_sport = lambda r: next((l["sport"] for l in r["legs"]), "Run")
    if target:  # race-week specifics
        drop(race_day)
        long_race = (tpred["total"] or 0) > 5400
        load = " Carb load day: 8-10 g carbs/kg." if long_race else ""
        around_race(
            race_day - ONE,
            "Day before your race: keep it light unless your coach says otherwise." + load,
            first_sport(target),
            1200,
            12.0,
            "Shakeout: 20 min easy with 3-4 short pickups." + load,
        )
        if long_race:
            for s in on(race_day - 2 * ONE):
                s[4] += " Carb load day 1: 8-10 g carbs/kg."
        weeks[-1]["sessions"] = [s for s in weeks[-1]["sessions"] if s[0] <= race_day]
    first_day, last_day = weeks[0]["start"], (race_day or weeks[-1]["start"] + 6 * ONE)
    for r in races:
        d = dt.date.fromisoformat(r["date"])
        if not first_day <= d <= last_day:
            continue
        pr = predict(p, r, ctl)
        if r is not target and (not target or r["id"] != target["id"]):
            drop(d)
            if r["priority"] == "B":
                around_race(
                    d - ONE,
                    "Meet tomorrow: keep it light unless your coach says otherwise.",
                    first_sport(r),
                    1200,
                    12.0,
                    "Pre-race shakeout: 20 min easy with pickups.",
                )
                for s in on(d - 2 * ONE):
                    if not is_team(s):
                        s[2] *= 0.6
                        s[3] *= 0.6
            around_race(
                d + ONE,
                "Day after a race: tell your coach how your legs feel.",
                first_sport(r),
                1800,
                15.0,
                "Post-race recovery: 30 min very easy, or rest.",
            )
        add(
            d,
            "Race",
            pr["total"] or 3600,
            race_tss(pr["total"]),
            f"{r['name']} ({r['priority']} race). See Races for pacing and fueling.",
            r["id"],
        )
    touched = set()
    for sc in sorted(scheduled or [], key=lambda x: x["date"]):  # the athlete's own sessions win over the plan's
        d = dt.date.fromisoformat(sc["date"])
        if not first_day <= d <= last_day:
            continue
        for w in weeks:
            w["sessions"] = [x for x in w["sessions"] if x[0] != d or x[1] == "Race"]
        IF, dur = SCHED_KINDS[sc["kind"]][0], sched_duration(p, sc) or 3600
        add(d, sc["sport"], dur, dur / 3600 * IF * IF * 100, sched_desc(p, sc), "s:" + sc["uid"])
        wk = next(w for w in weeks if w["start"] <= d < w["start"] + 7 * ONE)
        mine = lambda x: isinstance(x[5], str) or x[1] == "Race" or is_team(x)
        if sc["kind"] == "Long":  # one long session a week: the plan's own becomes an easy one
            same = [x for x in wk["sessions"] if x[1] == sc["sport"] and x[0] != d and not mine(x) and x[2] >= 3600]
            if same:
                x = max(same, key=lambda x: x[2])
                x[2] = max(1800, x[2] * 0.5)
                x[3] = x[2] / 3600 * 0.7**2 * 100
                x[4] = f"Easy {x[1].lower()} Z2, shorter this week: your long {sc['sport'].lower()} is on {d:%A}."
        if IF >= 0.85 or sc["kind"] == "Long":  # no hard session the day after a hard one
            for x in on(d + ONE):
                if not mine(x) and x[2] and x[3] / (x[2] / 3600) > 60:
                    x[3] = x[2] / 3600 * 0.7**2 * 100
                    x[4] = (
                        f"Easy {x[1].lower()} Z2, conversational: yesterday was your {sc['kind'].lower()} {sc['sport'].lower()}."
                    )
        touched.add(wk["start"])
    for wk in weeks:  # the week keeps its planned hours: what the athlete added is paid for by trimming the plan's own
        if wk["start"] not in touched:
            continue
        theirs = lambda x: isinstance(x[5], str) or x[1] == "Race" or is_team(x)
        mine_s = sum(x[2] for x in wk["sessions"] if theirs(x) and x[1] != "Race")
        ours = [x for x in wk["sessions"] if not theirs(x)]
        own_s = sum(x[2] for x in ours)
        if own_s and mine_s + own_s > wk["target_s"]:
            f = max(0.5, max(0.0, wk["target_s"] - mine_s) / own_s)
            if f < 0.97:
                for x in ours:
                    x[2], x[3] = x[2] * f, x[3] * f
                    if x[1] not in ("Rest", "Mobility", "Strength"):
                        x[4] += " Trimmed to fit the session you added."
    adapt_plan(p, weeks, issues or [])
    for w in weeks:
        w["sessions"] = sorted(
            (tuple(s) for s in w["sessions"] if s[0] >= first_day), key=lambda s: (s[0], s[1] == "Race")
        )
        w["hours"] = sum(s[2] for s in w["sessions"] if s[1] != "Race") / 3600
    return target, weeks


# ---------------------------------------------------------------- health: injuries, illness, fatigue


def issue_from_row(r):
    return dict(
        id=r["id"],
        kind=r["kind"],
        name=r["name"],
        area=r["area"] or "",
        side=r["side"] or "",
        severity=int(r["severity"] or 1),
        sports=json.loads(r["sports"] or "[]"),
        start=r["start"],
        end=r["end"] or None,
        ramp_days=r["ramp_days"],
        notes=r["notes"] or "",
    )


def gear_from_row(r):
    return dict(
        id=r["id"],
        name=r["name"],
        kind=r["kind"] or "Other",
        sports=json.loads(r["sports"] or "[]"),
        purchased=r["purchased"] or "",
        retire_km=r["retire_km"],
        active=bool(r["active"]),
        is_default=bool(r["is_default"]),
        notes=r["notes"] or "",
    )


def suggest_ramp_days(i, end=None):
    """How long the graded return should run: a floor from severity, stretched for an episode that dragged on -
    a few lost days barely need easing back into, a month out does."""
    sev = int(i["severity"] or 1)
    end = end or i.get("end")
    episode = (dt.date.fromisoformat(end) - dt.date.fromisoformat(i["start"])).days + 1 if end else 1
    return max(RAMP_BASE_DAYS.get(sev, 10), min(28, round(episode * 0.5)))


def active_on(issues, day):
    d = day.isoformat()
    return [i for i in issues if i["start"] <= d and (not i["end"] or d <= i["end"])]


def swap_sport(p, sport, restricted):
    for s in SWAP.get(sport, ["Bike", "Swim"]):
        if s in p["sports"] and s not in restricted:
            return s, SWAP_DESC[s]
    return "Other", "Cross-train: elliptical, aqua jogging or an upper-body erg, whichever is pain-free"


def adapt_session(p, s, issues):
    """Rewrite one planned session for active or recently resolved health issues. Returns a list of sessions."""
    day, sport, dur, tss, desc, rid = s
    if sport in ("Race", "Rest", "Mobility"):
        return [list(s)]
    act = active_on(issues, day)
    recent = [
        i
        for i in issues
        if i["end"] and 0 < (day - dt.date.fromisoformat(i["end"])).days <= (i.get("ramp_days") or DEFAULT_RAMP_DAYS)
    ]
    if not act and not recent:
        return [list(s)]
    notes, factor, easy, swapped = [], 1.0, False, None
    for i in act:
        k, sv, nm = i["kind"], i["severity"], i["name"]
        if sv >= 5 or (k == "Illness" and sv >= 3):
            why = (
                "No training with fever or symptoms below the neck."
                if k == "Illness"
                else "Recovery is the training today."
            )
            return [[day, "Rest", 0, 0.0, f"Rest: {nm}. {why}", None]]
        if k == "Illness":
            factor, easy = min(factor, 0.6), True
            notes.append(f"{nm}: easy only, stop if you feel worse")
        elif k == "Fatigue":
            factor, easy = min(factor, {1: 0.85, 2: 0.7, 3: 0.55, 4: 0.35}[sv]), True
            notes.append(f"{nm}: reduced load, no intensity")
        elif sport == "Strength":
            if sv >= 2:
                notes.append(f"{nm}: work around it with upper body, core and pain-free movements only")
        elif sport in i["sports"]:
            if sv == 1:
                easy = True
                notes.append(f"{nm}: keep it easy, stop if pain goes above 3/10")
            elif sv == 2:
                factor, easy = min(factor, 0.6), True
                notes.append(f"{nm}: shortened, and pain must stay under 3/10")
            elif not swapped:
                restricted = set().union(*(j["sports"] for j in act if j["kind"] in ("Injury", "Other")))
                swapped = swap_sport(p, sport, restricted)
                notes.append(f"Swapped from {sport.lower()} for {nm}: {swapped[1]}")
                if sv == 4:
                    factor, easy = min(factor, 0.6), True
    for i in recent:
        if i["kind"] == "Injury" and sport not in i["sports"]:
            continue
        since = (day - dt.date.fromisoformat(i["end"])).days
        ramp = i.get("ramp_days") or DEFAULT_RAMP_DAYS
        half = max(1, ramp // 2)  # first half of the ramp at half volume, second half at three-quarters
        f = (0.5 if since <= half else 0.75) if i["kind"] != "Fatigue" else 0.8
        factor, easy = min(factor, f), easy or since <= half
        notes.append(f"Returning after {i['name']}: {f:.0%} volume")
    if not notes:
        return [list(s)]
    hz = hr_zones(p)
    text = ". ".join(notes) + "."
    if easy:
        text += f" Keep it Z1-Z2 ({hz[1][1]:.0f}-{hz[1][2]:.0f} bpm), no intervals."
    text += f" Originally planned: {desc}"
    return [[day, swapped[0] if swapped else sport, dur * factor, tss * factor * (0.7 if easy else 1), text, rid]]


def adapt_plan(p, weeks, issues):
    """Apply health issues to every planned session, add daily rehab for injuries, collapse rest days."""
    if not issues:
        return
    for w in weeks:
        out = [x for s in w["sessions"] for x in adapt_session(p, s, issues)]
        for k in range(7):
            d = w["start"] + ONE * k
            inj = [i for i in active_on(issues, d) if i["kind"] == "Injury"]
            if inj:
                i = max(inj, key=lambda x: x["severity"])
                out.append(
                    [d, "Mobility", 900, 5.0, f"Rehab for {i['name']}: {BODY.get(i['area'], BODY['Other'])[1]}", None]
                )
        rest_days = {s[0] for s in out if s[1] == "Rest"}
        seen, kept = set(), []
        for s in out:
            if s[0] in rest_days and s[1] not in ("Rest", "Mobility", "Race"):
                continue
            if s[1] == "Rest" and s[0] in seen:
                continue
            if s[1] == "Rest":
                seen.add(s[0])
            kept.append(s)
        w["sessions"] = kept


def fatigue_signals(rows, series, today):
    """Warning signs of accumulated fatigue from the last 7 days vs a 4-week baseline."""

    def mean(rs, k):
        v = [r[k] for r in rs if r[k] is not None]
        return sum(v) / len(v) if v else None

    age = lambda r: (today - dt.date.fromisoformat(r["date"])).days
    last7 = [r for r in rows if 0 <= age(r) < 7]
    base = [r for r in rows if 7 <= age(r) < 35]
    last10 = [r for r in rows if 0 <= age(r) < 10]
    sig = []
    a, b = mean(last7, "rhr"), mean(base, "rhr")
    if a and b and a > b + 3:
        sig.append(f"Resting HR is up {a - b:.0f} bpm on your 4-week baseline")
    a, b = mean(last7, "hrv"), mean(base, "hrv")
    if a and b and a < b * 0.9:
        sig.append(f"HRV is {100 - a / b * 100:.0f}% below your 4-week baseline")
    f = [r["fatigue"] for r in last10 if r["fatigue"]]
    if len(f) >= 4 and sum(f) / len(f) >= 3.5:
        sig.append(f"You've rated fatigue {sum(f) / len(f):.1f}/5 on average over the last 10 days")
    a = mean(last7, "sleep_h")
    if a and a < 6.5:
        sig.append(f"Sleep is averaging {a:.1f} h over the last week")
    a = mean(last7, "soreness")
    if a and a >= 3.5:
        sig.append("Muscle soreness has stayed high all week")
    tsb14 = [x[3] for x in series[-14:]]
    if tsb14 and sum(tsb14) / len(tsb14) < -20:
        sig.append("Training stress balance has been below -20 for two weeks")
    return sig


def say(key, **kw):
    """One user-facing line from the catalog. Missing keys surface loudly rather than printing an empty box."""
    try:
        return COPY[key].format(**kw)
    except KeyError:
        return f"[missing copy: {key}]"


# ---------------------------------------------------------------- the coach: what today should actually be
# The plan is a template written weeks ago. This is the part that reads what you have actually done and how you
# have actually felt, and rewrites today before you see it. Everything here works from training load alone, so
# an athlete who never fills in a check-in still gets a real answer; check-ins sharpen it rather than unlock it.


def workout_if(dur_s, tss):
    """Intensity factor implied by a session's load and length. The inverse of TSS = hours * IF^2 * 100."""
    h = (dur_s or 0) / 3600
    return min(1.25, max(0.3, math.sqrt((tss or 0) / h / 100))) if h > 0.05 and tss else 0.65


def recovery_hours(dur_s, tss, sport):
    """How long a session needs before the body is square again.
    ponytail: a load-and-intensity curve fitted to the usual rules of thumb - a threshold hour costs about two
    days, an easy hour about half of one. A real EPOC model would need beat-by-beat HR we do not store."""
    if sport in ("Rest", "Mobility") or not tss:
        return 0.0
    IF = workout_if(dur_s, tss)
    return min(96.0, tss * (0.22 + 0.22 * IF))


def _ended_at(w, p):
    """When a logged session finished. Uses the recorded start when there is one, otherwise the hour this
    athlete usually trains, so the recovery clock is never wildly out."""
    day = dt.date.fromisoformat(w["date"])
    if w["start"]:
        try:
            return dt.datetime.fromisoformat(w["start"]) + dt.timedelta(seconds=w["dur_s"] or 0)
        except ValueError:
            pass
    return at(day, p.get("train_time", "07:00")) + dt.timedelta(seconds=w["dur_s"] or 0)


def recovery_clock(rows, p, now=None):
    """Hours of recovery still owed, and what is owing them. Sessions stack: the biggest debt counts in full and
    the rest add a share, because two hard days in a row cost more than the harder of the two alone."""
    now = now or dt.datetime.now()
    owed = []
    for w in rows:
        if not 0 <= (now.date() - dt.date.fromisoformat(w["date"])).days <= 5:
            continue  # filtered rather than broken out of: this must not depend on how rows are sorted
        full = recovery_hours(w["dur_s"], w["tss"], w["sport"])
        if full <= 0:
            continue
        left = full - (now - _ended_at(w, p)).total_seconds() / 3600
        if left > 0.5:
            owed.append((left, w))
    if not owed:
        return dict(hours=0.0, until="", items=[])
    owed.sort(reverse=True, key=lambda x: x[0])
    total = min(96.0, owed[0][0] + 0.35 * sum(x[0] for x in owed[1:]))  # stacked, but never more than four days
    return dict(
        hours=round(total, 1),
        until=(now + dt.timedelta(hours=total)).isoformat(timespec="minutes"),
        items=[
            dict(
                date=w["date"],
                sport=w["sport"],
                dur=hms(w["dur_s"] or 0),
                tss=round(w["tss"] or 0),
                left=round(left, 1),
            )
            for left, w in owed[:4]
        ],
    )


def load_state(rows, series, p, today=None, now=None):
    """Everything the coach reasons from: acute vs chronic load, how spiky and how monotonous the last week was,
    how many hard days are stacked up, how long since a genuine day off, and what is still owed in recovery."""
    today = today or dt.date.today()
    by_day, hard_days = {}, set()
    for w in rows:
        d = dt.date.fromisoformat(w["date"])
        by_day[d] = by_day.get(d, 0.0) + (w["tss"] or 0)
        if workout_if(w["dur_s"], w["tss"]) >= HARD_IF and (w["tss"] or 0) >= 35:
            hard_days.add(d)
    day = lambda n: by_day.get(today - ONE * n, 0.0)
    week = [by_day.get(today - ONE * i, 0.0) for i in range(7)]
    month = [by_day.get(today - ONE * i, 0.0) for i in range(28)]
    acute, chronic = sum(week) / 7, sum(month) / 28
    mean7 = acute
    sd7 = (sum((x - mean7) ** 2 for x in week) / 7) ** 0.5
    monotony = mean7 / sd7 if sd7 > 1 else (3.0 if mean7 > 10 else 0.0)  # every day the same is the risky shape
    streak = 0
    while (today - ONE * (streak + 1)) in hard_days and streak < 14:
        streak += 1
    if today in hard_days:
        streak += 1
    since_rest, d = 0, today if by_day.get(today, 0.0) > 0 else today - ONE
    while by_day.get(d, 0.0) > 0 and since_rest < 40:  # length of the run of days without one off
        since_rest, d = since_rest + 1, d - ONE
    return dict(
        today_tss=round(day(0)),
        yesterday_tss=round(day(1)),
        last48=round(day(0) + day(1)),
        last72=round(day(0) + day(1) + day(2)),
        week_tss=round(sum(week)),
        acwr=round(acute / chronic, 2) if chronic > 3 else None,
        monotony=round(monotony, 2),
        strain=round(sum(week) * monotony),
        hard_streak=streak,
        since_rest=since_rest,
        trained_today=day(0) > 0,
        tsb=round(series[-1][3]) if series else 0,
        ctl=round(series[-1][1]) if series else 0,
        recovery=recovery_clock(rows, p, now),
    )


def daily_advice(state, readiness_score, active_issues=(), today=None):
    """The verdict for today and, in plain words, every reason behind it. Reasons are ordered by how much they
    moved the answer, so the first line is always the one that actually decided it."""
    today = today or dt.date.today()
    rec, votes = state["recovery"], []
    vote = lambda level, why: votes.append((ORDER.index(level), level, why))
    hours, streak, rest_days = rec["hours"], state["hard_streak"], state["since_rest"]
    acwr, monotony, tsb = state["acwr"], state["monotony"], state["tsb"]
    if active_issues:
        worst = max(active_issues, key=lambda i: i["severity"])
        vote(
            "easy" if worst["severity"] <= 2 else "rest",
            say("advice.issue", name=worst["name"], severity=SEVERITY[worst["severity"]].lower()),
        )
    if streak >= 3:
        vote("rest", say("advice.streak.many", n=streak))
    elif streak == 2 and hours >= 14:
        vote("rest", say("advice.streak.owed", hours=hours))
    elif streak == 2:
        vote("easy", say("advice.streak.two"))
    if hours >= 30:
        vote("rest", say("advice.recovery.deep", hours=hours))
    elif hours >= 14:
        vote("easy", say("advice.recovery.some", hours=hours))
    elif hours >= 6:
        vote("moderate", say("advice.recovery.tail", hours=hours))
    if rest_days >= 12:
        vote("rest", say("advice.rest.none", n=rest_days))
    elif rest_days >= 8:
        vote("easy", say("advice.rest.few", n=rest_days))
    if acwr is not None:
        if acwr >= 1.6:
            vote("rest", say("advice.acwr.spike", acwr=acwr))
        elif acwr >= 1.35:
            vote("easy", say("advice.acwr.high", acwr=acwr))
        elif acwr < 0.8 and state["ctl"] > 25:
            vote("push", say("advice.acwr.low", acwr=acwr))
    if monotony >= 2.2 and state["week_tss"] > 250:
        vote("easy", say("advice.monotony", monotony=monotony))
    if readiness_score is not None:
        if readiness_score < 45:
            vote("rest", say("advice.ready.poor", score=readiness_score))
        elif readiness_score < 60:
            vote("easy", say("advice.ready.low", score=readiness_score))
        elif readiness_score < 75:
            vote("moderate", say("advice.ready.mid", score=readiness_score))
        elif readiness_score >= 88 and hours <= 3:
            vote("push", say("advice.ready.good", score=readiness_score))
    if tsb <= -35:
        vote("rest", say("advice.form.hole", tsb=tsb))
    elif tsb <= -22:
        vote("easy", say("advice.form.low", tsb=tsb))
    elif tsb >= 8 and state["ctl"] > 20:
        vote("push", say("advice.form.fresh", tsb=tsb))
    if not votes:
        vote("normal", say("advice.nothing"))
    votes.sort(key=lambda v: v[0])  # stable: within a level the earlier, more specific rule leads
    level = votes[0][1]
    # only reasons that argue for at least as much caution as the verdict belong in the explanation
    reasons = [w for i, lv, w in votes if i <= ORDER.index(level)] or [votes[0][2]]
    return dict(
        level=level,
        label=VERDICTS[level][0],
        reasons=reasons,
        others=[w for i, lv, w in votes if i > ORDER.index(level)],
    )


def adapt_for_load(p, sessions, advice, state):
    """Rewrite today's planned sessions to match the verdict. Mirrors adapt_session, which does the same job for
    injury and illness; this one answers to training load and recovery instead."""
    level = advice["level"]
    if level in ("normal", "push") or not sessions:
        return [list(s) for s in sessions]
    why = advice["reasons"][0]
    if level == "rest":
        planned = ", ".join(sorted({s[1] for s in sessions if s[1] not in ("Rest", "Race")}))
        text = (
            say("session.rest.had", why=why, planned=planned.lower()) if planned else say("session.rest.empty", why=why)
        )
        return [[sessions[0][0], "Rest", 0, 0.0, text, None]]
    factor = VERDICTS[level][1]
    hz, out = hr_zones(p), []
    for s in sessions:
        day, sport, dur, tss, desc, rid = s
        if sport in ("Race", "Rest"):
            out.append(list(s))
            continue
        if level == "easy":
            text = say("session.easy", why=why, lo=hz[1][1], hi=hz[1][2], was=desc)
            out.append([day, sport, dur * factor, tss * factor * 0.7, text, rid])
        else:
            out.append([day, sport, dur * factor, tss * factor * 0.85, say("session.moderate", why=why, was=desc), rid])
    return out


def training_status(rows, series, state, days_to_race=None):
    """Productive, overreaching, detraining and the rest - from the direction fitness is moving and what it is
    costing. Garmin calls this training status; the inputs are the same ones, the labels are the standard ones."""
    if len(series) < 21 or state["ctl"] < 5:
        return dict(status="No data", colour=STATUS_COLOUR["No data"], ramp=0.0, detail=say("status.none"))
    ramp = round(series[-1][1] - series[-8][1], 1)  # CTL change over the last week
    ramp4 = round(series[-1][1] - series[-29][1], 1) if len(series) > 29 else ramp
    tsb, acwr, ef = state["tsb"], state["acwr"], efficiency_trend(rows)
    if ramp <= -4:
        s, d = "Detraining", say("status.detraining", drop=abs(ramp))
    elif acwr is not None and acwr >= 1.5 or tsb <= -32:
        s, d = "Overreaching", say(
            "status.overreach.load" if acwr and acwr >= 1.5 else "status.overreach.form", tsb=tsb
        )
    elif tsb >= 5 and state["ctl"] >= 25 and (days_to_race is None or days_to_race <= 21):
        s, d = "Peaking", say("status.peaking")
    elif ramp >= 1.5 and tsb > -32:
        s, d = "Productive", say("status.productive", ramp=ramp)
    elif ramp >= 1.5 and ef is not None and ef < -3:
        s, d = "Unproductive", say("status.unproductive")
    elif state["week_tss"] < state["ctl"] * 4 and tsb > -10:
        s, d = "Recovery", say("status.recovery")
    else:
        s, d = "Maintaining", say("status.maintaining")
    return dict(status=s, colour=STATUS_COLOUR[s], ramp=ramp, ramp4=ramp4, ef=ef, detail=d)


def efficiency_trend(rows, today=None):
    """Percent change in aerobic efficiency - speed per heartbeat - over six weeks against the six before.
    Rising means the same pace is costing you less. Only steady aerobic sessions with heart rate count, because
    intervals and hills make the number meaningless."""
    today = today or dt.date.today()
    buckets = [[], []]
    for w in rows:
        if w["sport"] not in ("Run", "Bike", "Brick") or not w["avg_hr"] or not w["dist_km"] or not w["dur_s"]:
            continue
        if w["avg_hr"] < 90 or workout_if(w["dur_s"], w["tss"]) > 0.82 or w["dur_s"] < 1500:
            continue
        age = (today - dt.date.fromisoformat(w["date"])).days
        b = 0 if age < 42 else 1 if age < 84 else None
        if b is not None:
            buckets[b].append((w["dist_km"] * 1000 / w["dur_s"]) / w["avg_hr"] * 100)
    if len(buckets[0]) < 3 or len(buckets[1]) < 3:
        return None
    now, before = sum(buckets[0]) / len(buckets[0]), sum(buckets[1]) / len(buckets[1])
    return round((now / before - 1) * 100, 1)


# Easy / moderate / hard by intensity factor. The classic finding is that most training should sit in the first
# band; the middle one is where amateurs quietly lose the plot.
def intensity_mix(rows, today=None, days=28):
    """How the last four weeks split across easy, moderate and hard - by time, not session count."""
    today = today or dt.date.today()
    band = [0.0, 0.0, 0.0]
    for w in rows:
        if (today - dt.date.fromisoformat(w["date"])).days >= days or not w["dur_s"]:
            continue
        if w["sport"] in ("Rest", "Mobility", "Strength"):
            continue
        IF = workout_if(w["dur_s"], w["tss"])
        band[0 if IF < 0.75 else 1 if IF < 0.87 else 2] += w["dur_s"] / 3600
    total = sum(band)
    if total < 2:
        return None
    pct = [round(x / total * 100) for x in band]
    note = say(
        (
            "mix.polarised"
            if pct[0] >= 75 and pct[2] >= 5
            else "mix.grey" if pct[1] >= 30 else "mix.too_easy" if pct[2] < 4 else "mix.too_hard"
        ),
        moderate=pct[1],
        hard=pct[2],
    )
    return dict(
        hours=round(total, 1),
        easy=pct[0],
        moderate=pct[1],
        hard=pct[2],
        note=note,
        bands=[
            dict(name="Easy", pct=pct[0], hours=round(band[0], 1), colour="#12b76a"),
            dict(name="Moderate", pct=pct[1], hours=round(band[1], 1), colour="#f5b400"),
            dict(name="Hard", pct=pct[2], hours=round(band[2], 1), colour="#f03d3d"),
        ],
    )


def threshold_drift(p, recs):
    """Your bests say one thing, your saved thresholds say another. Surfaces the gap and the number to change,
    but never changes it - a PR can be a downhill course or a short GPS track, and only you know which."""
    out = []
    best = {e["key"]: e for e in recs["events"] if e.get("have") and e["sport"] == "Run"}
    for key, km in (("5k", 5.0), ("10k", 10.0), ("half", 21.0975)):
        e = best.get(key)
        if not e or not e["date"]:
            continue
        if (dt.date.today() - dt.date.fromisoformat(e["date"])).days > 120:
            continue
        implied = threshold_from_race(km, e["secs"])
        gain = p["run_thr_pace"] - implied
        if gain >= 4:  # at least four seconds a kilometre, otherwise it is noise
            out.append(
                dict(
                    what="Run threshold pace",
                    key="run_thr_pace",
                    now=fd("pace", p["run_thr_pace"]),
                    suggested=fd("pace", implied),
                    value=implied,
                    gain=f"{gain:.0f} s/km faster",
                    why=f"Your {e['label']} of {e['time']} on {_nice_date(dt.date.fromisoformat(e['date']))} implies it.",
                )
            )
            break
    return out


# ---------------------------------------------------------------- life: sleep, habits, reminders, motivation


def seed_life(db):
    """Default habits and the starter quote collection, once per database. Stamped as ancient (updated=1, rev=0) with
    fixed ids, so every device seeds identical rows and any real edit or delete from another device wins over them."""
    batches = ([("seeded_life", DEFAULT_QUOTES)] if not kv_get(db, "seeded_life") else []) + [
        (k, qs) for k, qs in QUOTE_BATCHES if not kv_get(db, k)
    ]
    if not batches:
        return
    db.execute("INSERT OR REPLACE INTO kv VALUES('applying', '1')")
    if not kv_get(db, "seeded_life"):
        for i, (uid, name) in enumerate(DEFAULT_HABITS):
            db.execute(
                "INSERT OR IGNORE INTO habits(uid, name, days, sort, updated, rev) VALUES(?,?,?,?,1,0)",
                (uid, name, json.dumps(list(range(7))), i),
            )
    for key, quotes in batches:
        for text, author in quotes:
            db.execute(
                "INSERT OR IGNORE INTO quotes(uid, text, author, updated, rev) VALUES(?,?,?,1,0)",
                ("q-" + hashlib.sha1(text.encode()).hexdigest()[:16], text, author),
            )
        db.execute("INSERT OR REPLACE INTO kv VALUES(?, '1')", (key,))
    db.execute("DELETE FROM kv WHERE k='applying'")
    db.commit()


def clock(s):
    """'HH:MM' (24 h) -> (h, m), validating."""
    h, m = (int(x) for x in str(s).strip().split(":"))
    if not (0 <= h < 24 and 0 <= m < 60):
        raise ValueError(s)
    return h, m


def at(day, hhmm):
    return dt.datetime.combine(day, dt.time(*clock(hhmm)))


def fmt12(t):
    return f"{t.hour % 12 or 12}:{t.minute:02d} {'AM' if t.hour < 12 else 'PM'}"


def sleep_goal(p):
    """Hours of sleep to plan for; 0 = auto (9 h for teens, whose need is 8-10 h; 8 h for adults)."""
    return float(p.get("sleep_goal") or (9 if int(p.get("age") or 30) < 18 else 8))


def wake_on(p, day):
    once = (p.get("wake_once") or {}).get(day.isoformat())  # one-off wake-up for a single date
    return at(day, once or (p["wake_weekday"] if day.weekday() in p.get("school_days", []) else p["wake_weekend"]))


def bedtime_before(p, day):
    """Lights-out time the night before `day` (so you wake at `day`'s wake time with your sleep goal banked)."""
    return wake_on(p, day) - dt.timedelta(hours=sleep_goal(p))


def streak(done_dates, sched, today):
    """Consecutive scheduled days done, ending today (or yesterday if today isn't done yet). Unscheduled days skip."""
    d, n = today, 0
    if today.weekday() in sched and today.isoformat() not in done_dates:
        d -= ONE
    for _ in range(400):
        if d.weekday() in sched:
            if d.isoformat() not in done_dates:
                break
            n += 1
        d -= ONE
    return n


# ---------------------------------------------------------------- nutrition


def bmr(p):
    return 10 * p["weight_kg"] + 6.25 * p["height_cm"] - 5 * p["age"] + (5 if p["sex"] == "M" else -161)


def daily_nutrition(p, sessions, goal):
    """sessions: [(sport, dur_s, kcal)]. Carb targets per ACSM/IOC g/kg ranges by training volume."""
    kg = p["weight_kg"]
    h = sum(s[1] for s in sessions) / 3600
    train = sum(s[2] for s in sessions)
    tdee = bmr(p) * ACTIVITY.get(p.get("activity"), 1.35) + train
    kcal = tdee + {"lose": -400 if h < 1.5 else -200, "gain": 300}.get(goal, 0)
    cpk = 3.5 if h == 0 else 5 if h < 1 else 6.5 if h < 2 else 8 if h < 3 else 10
    if goal == "lose" and h < 1.5:
        cpk -= 1
    protein = kg * (p.get("protein_gkg") or (2.2 if goal == "lose" else 1.8))
    carbs = kg * cpk
    fat = (kcal - 4 * carbs - 4 * protein) / 9
    if fat < 0.8 * kg:  # keep fat at a healthy floor; trim carbs (not below 3 g/kg) to stay near target
        fat = 0.8 * kg
        carbs = max(3 * kg, (kcal - 4 * protein - 9 * fat) / 4)
    kcal = 4 * carbs + 4 * protein + 9 * fat
    return dict(
        hours=h,
        train_kcal=train,
        bmr=bmr(p),
        life=bmr(p) * (ACTIVITY.get(p.get("activity"), 1.35) - 1),
        tdee=tdee,
        kcal=kcal,
        carbs=carbs,
        protein=protein,
        fat=fat,
        cpk=carbs / kg,
    )


def carbs_per_hour(p, total_h, sport):
    if sport == "Swim":
        return 0
    c = 0 if total_h < 1 else 30 if total_h < 1.5 else 60 if total_h < 2.5 else min(90, p["gut_carbs"])
    return min(c, 60) if sport == "Run" and total_h < 2.5 else min(c, p["gut_carbs"])


def fuel_session(p, sport, dur_s, IF=0.72, hot=False):
    kg, h, gel = p["weight_kg"], dur_s / 3600, p.get("gel_carbs") or 25
    if h <= 0 or sport in ("Rest", "Race", "Strength", "Mobility"):
        return []
    L = []
    if h >= 1.25:
        L.append(f"Before: {1 * kg:.0f}-{2 * kg:.0f} g carbs 2-3 h out, low fibre/fat.")
    else:
        L.append("Before: normal meal 2-3 h out, or a 20-30 g carb snack if training fasted-ish.")
    carbs = carbs_per_hour(p, h, sport) if sport != "Swim" else (30 if h >= 1.5 else 0)
    fluid = min(p["sweat_rate"] * 0.75 * (1.25 if hot else 1), 1.2)
    if h >= 1 and sport != "Swim":
        L.append(
            f"During: ~{carbs:.0f} g carbs/h (~{carbs / gel:.1f} gels/h), {fd('vol', fluid)}/h fluid, "
            f"~{fluid * p['sweat_na']:.0f} mg sodium/h."
        )
    elif h >= 0.75:
        L.append("During: water to thirst" + (f"; {carbs:.0f} g carbs/h" if carbs else "") + ".")
    if h >= 1 or IF >= 0.85:
        L.append(f"After: {0.3 * kg:.0f} g protein + {1.0 * kg:.0f} g carbs within ~1 h; drink ~1.5x fluid lost.")
    return L


CAFFEINE_MG_PER_KG = {"low": 6.0, "normal": 4.5, "high": 3.0}  # sensitivity -> where in the 3-6 mg/kg band to sit
CAFFEINE_CAP_MG = 400.0  # FDA/EFSA generally-safe daily ceiling for a healthy adult - a dose never exceeds this


def caffeine_dose(p, dur_s):
    """Pre-session caffeine, scaled to body weight and split across long events. Not medical advice."""
    kg = p["weight_kg"]
    sens = p.get("caffeine_sensitivity") or "normal"
    mgkg = CAFFEINE_MG_PER_KG.get(sens, 4.5)
    raw = kg * mgkg
    total = min(raw, CAFFEINE_CAP_MG)
    h = (dur_s or 0) / 3600
    if h >= 3:  # split so the second half still has it on board, rather than one big jittery hit
        pre = round(total * 0.6 / 5) * 5
        splits = [
            dict(when="45-60 min before", mg=round(pre)),
            dict(when=f"~{hms(dur_s / 2)} in (halfway)", mg=round(total - pre)),
        ]
    else:
        splits = [dict(when="45-60 min before", mg=round(total))]
    return dict(
        mg=round(total),
        mg_per_kg=round(total / kg, 1),
        sensitivity=sens,
        splits=splits,
        capped=raw > CAFFEINE_CAP_MG + 1e-6,
        basis=(
            f"{mgkg:.1f} mg/kg (within the usual 3-6 mg/kg sports-nutrition range for your {sens} sensitivity), "
            f"capped at {CAFFEINE_CAP_MG:.0f} mg - above that the side-effect risk (jitters, GI upset, racing heart) "
            "rises faster than any further performance benefit."
        ),
    )


def caffeine_deload(p, days_out=None):
    """Optional taper of habitual caffeine before a race, so the race-day dose still has a real effect."""
    habitual = p.get("caffeine_mg") or 0
    if habitual < 100:
        return dict(
            needed=False, days=0, note="Habitual intake is low enough that race day will already feel like a boost."
        )
    days = 3 if habitual < 300 else 5
    if days_out is not None and days_out < days:
        return dict(
            needed=True,
            days=days_out,
            note=f"Only {days_out} day(s) out - taper what you can; a full taper is {days} days "
            "for your habitual intake.",
        )
    return dict(
        needed=True,
        days=days,
        note=(
            f"Starting {days} days before the race, cut your usual caffeine roughly in half each day toward zero. "
            "Taper rather than quit cold - that avoids withdrawal headaches and fatigue clouding race week."
        ),
    )


def race_fueling(p, race, pred):
    kg, gel = p["weight_kg"], p.get("gel_carbs") or 25
    total_h = (pred["total"] or 3600) / 3600
    fluid = min(p["sweat_rate"] * 0.75 * (1.25 if race.get("temp_c", 18) >= 24 else 1), 1.2)
    na = fluid * p["sweat_na"]
    tl, grams = [], 0.0
    if total_h >= 2.5:
        tl.append(
            (
                "2 days out",
                "Carb load",
                f"{8 * kg:.0f}–{10 * kg:.0f} g carbs/day (8–10 g/kg). Rice, bagels, pasta, juice. Cut fibre and fat.",
            )
        )
    elif total_h >= 1.25:
        tl.append(
            ("Day before", "Carb up", f"{7 * kg:.0f}–{8 * kg:.0f} g carbs (7–8 g/kg). Familiar, low-fibre foods.")
        )
    tl.append(
        (
            "−3 h",
            "Breakfast",
            f"{(2 if total_h >= 1.25 else 1) * kg:.0f}–{(3 if total_h >= 1.25 else 2) * kg:.0f} g carbs + ~{fd('vol', 0.5)} fluid. Bagel + honey + banana + sports drink.",
        )
    )
    caf = caffeine_dose(p, pred["total"] or 3600)
    if p.get("caffeine_mg"):
        try:
            days_out = (dt.date.fromisoformat(race["date"]) - dt.date.today()).days
        except (KeyError, ValueError, TypeError):
            days_out = None
        deload = caffeine_deload(p, days_out)
        if deload["needed"] and (days_out is None or 0 < days_out <= deload["days"] + 1):
            tl.append((f"{deload['days']} days out", "Caffeine deload", deload["note"]))
    tl.append(
        (
            "45-60 min before",
            "Caffeine (optional)",
            f"{caf['splits'][0]['mg']:.0f} mg, only if practised. {caf['basis']}",
        )
    )
    if total_h >= 1:
        tl.append(("−15 min", "Pre-start gel", f"One gel (~{gel:.0f} g carbs) + a few sips of water."))
        grams += gel
    for s in pred["segs"]:
        if s["kind"] != "leg" or not s["secs"]:
            continue
        h = s["secs"] / 3600
        c = carbs_per_hour(p, total_h, s["sport"])
        if s["sport"] == "Swim":
            continue
        grams += c * h
        extra = " Mix in real food (potatoes, rice balls, bars) — aim 250-350 kcal/h." if total_h > 6 else ""
        tl.append(
            (
                s["sport"],
                f"{c:.0f} g carbs/h" if c else "Water / mouth rinse",
                (
                    f"{c * h:.0f} g over {hms(s['secs'])} (~{c * h / gel:.0f} gels or drink-mix equivalent). "
                    if c
                    else ""
                )
                + f"{fd('vol', fluid)}/h fluid, ~{na:.0f} mg sodium/h."
                + extra,
            )
        )
    if len(caf["splits"]) > 1:
        sp = caf["splits"][1]
        tl.append(
            (
                sp["when"],
                "Caffeine (optional)",
                f"{sp['mg']:.0f} mg - the rest of the dose, split rather than taken all at once.",
            )
        )
    tl.append(
        (
            "Finish",
            "Recovery",
            f"{0.3 * kg:.0f} g protein + {1.2 * kg:.0f} g carbs in the first hour, then normal meals.",
        )
    )
    peak = max([carbs_per_hour(p, total_h, s["sport"]) for s in pred["segs"] if s["kind"] == "leg"] + [0])
    tiles = [
        dict(label="Total race carbs", value=f"{grams:.0f} g", sub=f"~{grams / gel:.0f} gel-equivalents"),
        dict(label="Peak carb rate", value=f"{peak:.0f} g/h", sub=f"gut-trained to {p['gut_carbs']:.0f} g/h"),
        dict(label="Fluid", value=f"{fd('vol', fluid)}/h", sub=f"sweat rate {fd('vol', p['sweat_rate'])}/h"),
        dict(label="Sodium", value=f"{na:.0f} mg/h", sub=f"@ {p['sweat_na']:.0f} mg/L sweat"),
    ]
    return dict(
        tiles=tiles,
        timeline=[dict(when=a, what=b, detail=c) for a, b, c in tl],
        note="Only use products you've trained with. Redo the sweat test in race-like heat.",
    )


# ---------------------------------------------------------------- activity file import


def _tag(e):
    return e.tag.rsplit("}", 1)[-1]


def _child(e, name):
    for c in e:
        if _tag(c) == name:
            return c
    return None


def _haversine(a, b):
    la1, lo1, la2, lo2 = map(math.radians, (a[0], a[1], b[0], b[1]))
    h = math.sin((la2 - la1) / 2) ** 2 + math.cos(la1) * math.cos(la2) * math.sin((lo2 - lo1) / 2) ** 2
    return 6371.0 * 2 * math.asin(math.sqrt(h))


def _sport_from(s):
    s = (s or "").lower()
    for keys, sport in (
        (("run",), "Run"),
        (("bik", "cycl", "rid"), "Bike"),
        (("swim",), "Swim"),
        (("row",), "Row"),
        (("ski",), "Ski"),
        (("hik",), "Hike"),
        (("walk",), "Walk"),
        (("paddl", "kayak", "canoe"), "Paddle"),
    ):
        if any(k in s for k in keys):
            return sport
    return "Other"


def parse_activity(path):
    """TCX or GPX -> dict(date, sport, dur_s, dist_km, avg_hr, avg_w). FIT: export as TCX from Garmin Connect/Strava."""
    root = ET.parse(path).getroot()
    hrs, watts = [], []
    if path.lower().endswith(".tcx"):
        act = next(e for e in root.iter() if _tag(e) == "Activity")
        dur = dist = 0.0
        start = None
        for e in act.iter():
            t = _tag(e)
            if t == "Lap":
                start = start or e.get("StartTime")
                c = _child(e, "TotalTimeSeconds")
                dur += float(c.text) if c is not None else 0
                c = _child(e, "DistanceMeters")
                dist += float(c.text) / 1000 if c is not None else 0
            elif t == "HeartRateBpm":
                c = _child(e, "Value")
                if c is not None:
                    hrs.append(float(c.text))
            elif t == "Watts" and e.text:
                watts.append(float(e.text))
        sport = _sport_from(act.get("Sport"))
    else:
        pts, sport = [], "Other"
        for e in root.iter():
            t = _tag(e)
            if t == "type" and e.text:
                sport = _sport_from(e.text)
            elif t == "trkpt":
                tm = None
                for c in e.iter():
                    ct = _tag(c)
                    if ct == "time":
                        tm = dt.datetime.fromisoformat(c.text.strip())
                    elif ct == "hr" and c.text:
                        hrs.append(float(c.text))
                    elif ct == "power" and c.text:
                        watts.append(float(c.text))
                pts.append((float(e.get("lat")), float(e.get("lon")), tm))
        if len(pts) < 2:
            raise ValueError("no track points")
        dist = sum(_haversine(pts[i], pts[i + 1]) for i in range(len(pts) - 1))
        dur = (pts[-1][2] - pts[0][2]).total_seconds() if pts[0][2] and pts[-1][2] else 0
        start = pts[0][2].isoformat() if pts[0][2] else None
        if sport == "Other" and dur:
            kmh = dist / (dur / 3600)
            sport = "Bike" if kmh > 16 else "Run" if kmh > 5 else "Other"
    local = _local(dt.datetime.fromisoformat(start.strip())) if start else None
    return dict(
        date=(local.date() if local else dt.date.today()).isoformat(),
        start=_stamp(local),
        sport=sport,
        dur_s=dur,
        dist_km=dist,
        avg_hr=sum(hrs) / len(hrs) if hrs else None,
        avg_w=sum(watts) / len(watts) if watts else None,
        notes="Imported: " + os.path.basename(path),
    )


def _local(t):
    """Aware timestamps (device files, Strava's UTC export) -> this computer's local time; naive ones are already local."""
    return t.astimezone().replace(tzinfo=None) if t.tzinfo else t


def _stamp(t):
    return t.strftime("%Y-%m-%dT%H:%M") if t else None


def parse_strava_csv(path):
    """activities.csv from a Strava account export -> ([activity dicts], bad row count).
    Strava repeats some headers: the first 'Distance' is in display units (metres for swims), a later one
    in metres. Times are UTC."""
    with open(path, newline="", encoding="utf-8-sig") as fh:
        rows = list(csv.reader(fh))
    if not rows:
        raise ValueError("empty file")
    cols = {}
    for i, h in enumerate(rows[0]):
        cols.setdefault(h.strip(), []).append(i)
    if "Activity Date" not in cols or "Activity Type" not in cols:
        raise ValueError(
            "not a Strava activities.csv (get it from Strava: Settings > My Account > Download your archive)"
        )

    def get(r, name, last=False):
        idx = cols.get(name)
        if not idx:
            return ""
        i = idx[-1] if last else idx[0]
        return r[i].strip() if i < len(r) else ""

    def number(s):
        s = s.replace(",", "")
        return float(s) if s else 0.0

    out, bad = [], 0
    for r in rows[1:]:
        if not any(x.strip() for x in r):
            continue
        try:
            raw = get(r, "Activity Date").replace(" ", " ")  # newer exports use a narrow space before AM/PM
            when = _strptime_any(raw, STRAVA_DATE_FORMATS)
            if when is None:
                raise ValueError(raw)
            start = _local(when.replace(tzinfo=dt.timezone.utc))
            kind = get(r, "Activity Type")
            sport = STRAVA_TYPES.get(kind.replace(" ", "").lower()) or _sport_from(kind)
            dur = number(get(r, "Moving Time")) or number(get(r, "Elapsed Time"))
            if len(cols.get("Distance", [])) > 1 and get(r, "Distance", last=True):
                km = number(get(r, "Distance", last=True)) / 1000
            else:
                km = number(get(r, "Distance"))
                km = km / 1000 if sport == "Swim" and km > 20 else km  # swims are listed in metres
            watts = number(get(r, "Weighted Average Power")) or number(get(r, "Average Watts"))
            note = " · ".join(x for x in (get(r, "Activity Name"), get(r, "Activity Description")) if x)
            if dur <= 0:
                raise ValueError("no duration")
            out.append(
                dict(
                    date=start.date().isoformat(),
                    start=_stamp(start),
                    sport=sport,
                    dur_s=dur,
                    dist_km=km,
                    avg_hr=number(get(r, "Average Heart Rate")) or None,
                    avg_w=watts or None,
                    notes=note or "Imported from Strava",
                    indoor="virtual" in kind.lower(),
                )
            )
        except (ValueError, IndexError):
            bad += 1
    return out, bad


def _strptime_any(s, formats):
    for f in formats:
        try:
            return dt.datetime.strptime(s, f)
        except ValueError:
            pass
    return None


def health_to_data(workouts, samples):
    """Apple Health workouts + samples -> (activities for _import_activities, {date: wellness fields}).
    Daily values land on the local date the sample ends (so last night's sleep counts for this morning).
    Sleep is summed per source and the largest source wins, so iPhone + Watch don't double-count a night."""
    iso = lambda x: _local(dt.datetime.fromisoformat(x.replace("Z", "+00:00")))
    acts = []
    for w in workouts:
        sport = HEALTH_SPORTS.get(w.get("workoutType"), "Other")
        if not sport or not w.get("duration"):
            continue
        # a few seconds with no distance is a stray start, not a run (a 100 m sprint is short but has distance)
        if float(w["duration"]) < 30 and not w.get("totalDistance"):
            continue
        start = iso(w["startDate"])
        acts.append(
            dict(
                date=start.date().isoformat(),
                start=_stamp(start),
                sport=sport,
                dur_s=float(w["duration"]),
                dist_km=(w.get("totalDistance") or 0) / 1000,
                avg_hr=w.get("avgHr") or None,
                avg_w=None,
                notes=f"Apple Health · {w.get('sourceName') or 'Workout'}",
            )
        )
    per, sleep = {}, {}
    for x in samples:
        d = iso(x["endDate"]).date().isoformat()
        kind = x.get("dataType")
        if kind == "sleep":
            if x.get("sleepState") in ("asleep", "rem", "deep", "light"):
                src = sleep.setdefault(d, {})
                src[x.get("sourceName", "")] = src.get(x.get("sourceName", ""), 0) + float(x["value"])
        elif kind in ("restingHeartRate", "heartRateVariability", "weight"):
            per.setdefault(d, {}).setdefault(kind, []).append(float(x["value"]))
    daily = {}
    for d in set(per) | set(sleep):
        v = per.get(d, {})
        mean = lambda k: round(sum(v[k]) / len(v[k]), 1) if v.get(k) else None
        daily[d] = dict(
            rhr=mean("restingHeartRate"),
            hrv=mean("heartRateVariability"),
            weight_kg=v["weight"][-1] if v.get("weight") else None,
            sleep_h=round(max(sleep[d].values()) / 60, 2) if d in sleep else None,
        )
    return acts, daily


def is_duplicate(a, b):
    """Same day + same sport + (distance within 5%, or duration within 10% when distance is missing).
    When both have start times they must also start within an hour, so a genuine AM/PM double is kept.
    ponytail: without start times two identical sessions on one day look like a duplicate; manual entries have none."""
    if a["date"] != b["date"] or SPORT_FAMILY.get(a["sport"], a["sport"]) != SPORT_FAMILY.get(b["sport"], b["sport"]):
        return False
    if a.get("start") and b.get("start"):
        gap = abs(dt.datetime.fromisoformat(a["start"]) - dt.datetime.fromisoformat(b["start"]))
        if gap > dt.timedelta(hours=1):
            return False
    da, db = a.get("dist_km") or 0, b.get("dist_km") or 0
    if da > 0 and db > 0:
        return abs(da - db) / max(da, db) <= 0.05
    ta, tb = a.get("dur_s") or 0, b.get("dur_s") or 0
    return max(ta, tb) > 0 and abs(ta - tb) / max(ta, tb) <= 0.10


# ---------------------------------------------------------------- storage


def open_db(path=DB_PATH):
    if path != ":memory:":
        os.makedirs(os.path.dirname(path), exist_ok=True)
    db = sqlite3.connect(path, check_same_thread=False)  # the Api serialises access with a lock
    db.row_factory = sqlite3.Row
    db.executescript(SCHEMA)
    if "start" not in [c[1] for c in db.execute("PRAGMA table_info(workouts)")]:
        db.execute("ALTER TABLE workouts ADD COLUMN start TEXT")  # local start time, used for duplicate detection
    have = [c[1] for c in db.execute("PRAGMA table_info(wellness)")]
    for col in ("fatigue", "mood"):
        if col not in have:
            db.execute(f"ALTER TABLE wellness ADD COLUMN {col} INTEGER")
    for col, typ in (
        ("wx_temp", "REAL"),
        ("wx_dew", "REAL"),
        ("wx_code", "INTEGER"),
        ("indoor", "INTEGER DEFAULT 0"),
        ("splits", "TEXT"),
        ("gear_id", "INTEGER"),
    ):
        if col not in [c[1] for c in db.execute("PRAGMA table_info(workouts)")]:
            db.execute(f"ALTER TABLE workouts ADD COLUMN {col} {typ}")
    if "start" not in [c[1] for c in db.execute("PRAGMA table_info(races)")]:
        db.execute("ALTER TABLE races ADD COLUMN start TEXT")
    if "ramp_days" not in [c[1] for c in db.execute("PRAGMA table_info(issues)")]:
        db.execute("ALTER TABLE issues ADD COLUMN ramp_days INTEGER")
    db.execute("CREATE INDEX IF NOT EXISTS workouts_date ON workouts(date)")
    add_sync_columns(db)
    db.commit()
    seed_life(db)
    return db


def now_ms():
    return int(time.time() * 1000)


def kv_get(db, k, default=None):
    row = db.execute("SELECT v FROM kv WHERE k=?", (k,)).fetchone()
    return row[0] if row else default


def current_rev(db):
    return int(kv_get(db, "rev", 0))


def bump_rev(db):
    db.execute("UPDATE kv SET v=CAST(v AS INTEGER)+1 WHERE k='rev'")
    return current_rev(db)


def add_sync_columns(db):
    db.execute(
        "CREATE TABLE IF NOT EXISTS tombstones(tbl TEXT, key TEXT, updated INTEGER, rev INTEGER, PRIMARY KEY(tbl, key))"
    )
    db.execute("INSERT OR IGNORE INTO kv VALUES('rev', '0')")
    db.execute("DELETE FROM kv WHERE k='applying'")  # a crash mid-sync must not disable change tracking
    for t, key in SYNC_TABLES.items():
        have = [c[1] for c in db.execute(f"PRAGMA table_info({t})")]
        for col, typ in (("uid", "TEXT"), ("updated", "INTEGER"), ("rev", "INTEGER")):
            if col not in have and not (col == "uid" and key != "uid"):
                db.execute(f"ALTER TABLE {t} ADD COLUMN {col} {typ}")
        if key == "uid":
            db.execute(f"CREATE UNIQUE INDEX IF NOT EXISTS {t}_uid ON {t}(uid)")
        stamp = (
            f"UPDATE kv SET v=CAST(v AS INTEGER)+1 WHERE k='rev'; "
            f"UPDATE {t} SET {'uid=COALESCE(uid, lower(hex(randomblob(16)))), ' if key == 'uid' else ''}"
            f"updated={NOW_MS}, rev=(SELECT CAST(v AS INTEGER) FROM kv WHERE k='rev') WHERE rowid=NEW.rowid; "
        )
        db.execute(
            f"CREATE TRIGGER IF NOT EXISTS {t}_sync_ins AFTER INSERT ON {t} WHEN {LOCAL} BEGIN {stamp}"
            f"DELETE FROM tombstones WHERE tbl='{t}' AND key=(SELECT {key} FROM {t} WHERE rowid=NEW.rowid); END"
        )
        db.execute(f"CREATE TRIGGER IF NOT EXISTS {t}_sync_upd AFTER UPDATE ON {t} WHEN {LOCAL} BEGIN {stamp} END")
        db.execute(
            f"CREATE TRIGGER IF NOT EXISTS {t}_sync_del AFTER DELETE ON {t} WHEN {LOCAL} BEGIN "
            f"UPDATE kv SET v=CAST(v AS INTEGER)+1 WHERE k='rev'; "
            f"INSERT OR REPLACE INTO tombstones VALUES('{t}', OLD.{key}, {NOW_MS}, (SELECT CAST(v AS INTEGER) FROM kv WHERE k='rev')); END"
        )
        # rows from before sync existed: the update trigger gives them a uid, timestamp and rev
        db.execute(f"UPDATE {t} SET updated=NULL WHERE updated IS NULL{' OR uid IS NULL' if key == 'uid' else ''}")


def collect_changes(db, since):
    """Everything this database changed after rev `since`, in a device-independent form."""
    rows = {}
    for t in SYNC_TABLES:
        rows[t] = [
            {k: v for k, v in dict(r).items() if k not in ("id", "rev")}
            for r in db.execute(f"SELECT * FROM {t} WHERE rev > ?", (since,))
        ]
    tombs = [
        dict(tbl=r["tbl"], key=r["key"], updated=r["updated"])
        for r in db.execute("SELECT * FROM tombstones WHERE rev > ?", (since,))
    ]
    profile = None
    if int(kv_get(db, "profile_rev", 0)) > since:
        data = {k: v for k, v in json.loads(kv_get(db, "profile", "{}")).items() if k not in LOCAL_KEYS}
        profile = dict(data=data, updated=int(kv_get(db, "profile_updated", 0)))
    return dict(rows=rows, tombstones=tombs, profile=profile, rev=current_rev(db))


def apply_changes(db, ch, hub):
    """Merge another device's changes, last writer wins per row. The hub gives merged rows a fresh rev so other
    devices receive them; a phone stores them with rev 0 so they aren't echoed back.
    ponytail: wall-clock timestamps and whole-profile merges; switch to hybrid logical clocks / per-field profile merge
    if devices with badly wrong clocks or simultaneous settings edits become a real problem."""
    n = 0
    db.execute("INSERT OR REPLACE INTO kv VALUES('applying', '1')")
    try:
        for t, rows in (ch.get("rows") or {}).items():
            if t not in SYNC_TABLES:
                continue
            key = SYNC_TABLES[t]
            cols = {c[1] for c in db.execute(f"PRAGMA table_info({t})")} - {"id", "rev"}
            for r in rows:
                r = {k: v for k, v in r.items() if k in cols}
                if not r.get(key) or not r.get("updated"):
                    continue
                tomb = db.execute("SELECT updated FROM tombstones WHERE tbl=? AND key=?", (t, r[key])).fetchone()
                local = db.execute(f"SELECT updated FROM {t} WHERE {key}=?", (r[key],)).fetchone()
                if (tomb and tomb[0] >= r["updated"]) or (local and (local[0] or 0) >= r["updated"]):
                    continue
                r["rev"] = bump_rev(db) if hub else 0
                names = ",".join(f'"{c}"' for c in r)
                if local:
                    sets = ",".join(f'"{c}"=?' for c in r)
                    db.execute(f"UPDATE {t} SET {sets} WHERE {key}=?", [*r.values(), r[key]])
                else:
                    db.execute(f"INSERT INTO {t}({names}) VALUES({','.join('?' * len(r))})", list(r.values()))
                db.execute("DELETE FROM tombstones WHERE tbl=? AND key=?", (t, r[key]))
                n += 1
        for tb in ch.get("tombstones") or []:
            t = tb.get("tbl")
            if t not in SYNC_TABLES:
                continue
            key = SYNC_TABLES[t]
            local = db.execute(f"SELECT updated FROM {t} WHERE {key}=?", (tb["key"],)).fetchone()
            mine = db.execute("SELECT updated FROM tombstones WHERE tbl=? AND key=?", (t, tb["key"])).fetchone()
            if (local and (local[0] or 0) > tb["updated"]) or (mine and mine[0] >= tb["updated"]):
                continue  # edited after the delete (edit wins), or already deleted
            db.execute(f"DELETE FROM {t} WHERE {key}=?", (tb["key"],))
            db.execute(
                "INSERT OR REPLACE INTO tombstones VALUES(?,?,?,?)",
                (t, tb["key"], tb["updated"], bump_rev(db) if hub else 0),
            )
            n += local is not None
        pr = ch.get("profile")
        if pr and pr.get("updated", 0) > int(kv_get(db, "profile_updated", 0)):
            mine = json.loads(kv_get(db, "profile", "{}"))
            merged = {**pr["data"], **{k: v for k, v in mine.items() if k in LOCAL_KEYS}}
            db.execute("INSERT OR REPLACE INTO kv VALUES('profile', ?)", (json.dumps(merged),))
            db.execute("INSERT OR REPLACE INTO kv VALUES('profile_updated', ?)", (str(pr["updated"]),))
            db.execute("INSERT OR REPLACE INTO kv VALUES('profile_rev', ?)", (str(bump_rev(db) if hub else 0),))
            n += 1
    finally:
        db.execute("DELETE FROM kv WHERE k='applying'")
    db.commit()
    return n


def lan_addresses():
    import socket

    ips = set()
    try:
        s_ = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s_.connect(("10.255.255.255", 1))  # no packet is sent; this just picks the outward-facing interface
        ips.add(s_.getsockname()[0])
        s_.close()
    except OSError:
        pass
    try:
        ips.update(socket.gethostbyname_ex(socket.gethostname())[2])
    except OSError:
        pass
    return sorted(ip for ip in ips if not ip.startswith(("127.", "169.254.")))


def new_pairing_code():
    import secrets

    alphabet = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"
    c = "".join(secrets.choice(alphabet) for _ in range(8))
    return f"{c[:4]}-{c[4:]}"


def backup_db(path, keep=20):
    """Copy the DB to backups/ (sqlite online backup, safe while open). Keeps the newest `keep`."""
    if not os.path.exists(path):
        return None
    folder = os.path.join(os.path.dirname(path), "backups")
    os.makedirs(folder, exist_ok=True)
    dst = os.path.join(folder, f"data-{dt.datetime.now():%Y%m%d-%H%M%S}.db")
    src, out = sqlite3.connect(path), sqlite3.connect(dst)
    src.backup(out)
    out.close()
    src.close()
    for old in sorted(glob.glob(os.path.join(folder, "data-*.db")))[:-keep]:
        os.remove(old)
    return dst


def load_profile(db):
    row = db.execute("SELECT v FROM kv WHERE k='profile'").fetchone()
    P.clear()
    P.update(DEFAULTS)
    stored = json.loads(row["v"]) if row else {}
    # v1/v2 kept a single race inside the profile: move it to the races table once
    if "race_name" in stored and not db.execute("SELECT 1 FROM races").fetchone():
        preset = OLD_RACE_TYPES.get(stored.get("race_type"), "70.3 / half-distance triathlon")
        legs = [
            dict(sport=s, km=km, elev=stored.get("elev_gain", 0) if s == "Bike" else 0) for s, km in PRESETS[preset][1]
        ]
        db.execute(
            "INSERT INTO races(name,date,preset,legs,priority,temp_c,t1,t2,goal_s,result_s,notes) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?)",
            (
                stored["race_name"],
                stored.get("race_date", dt.date.today().isoformat()),
                preset,
                json.dumps(legs),
                "A",
                stored.get("temp_c", 20),
                stored.get("t1", 180),
                stored.get("t2", 120),
                None,
                None,
                "",
            ),
        )
    for k in ("race_name", "race_date", "race_type", "elev_gain", "temp_c", "t1", "t2"):
        stored.pop(k, None)
    if row and "setup_done" not in stored:
        stored["setup_done"] = True  # existing athlete from an earlier version
    # races used to be referenced by local row number; sync needs their permanent ids
    uid_of = {r["id"]: r["uid"] for r in db.execute("SELECT id, uid FROM races")}
    if isinstance(stored.get("plan_race"), int):
        stored["plan_race"] = uid_of.get(stored["plan_race"], "")
    stored["checklist"] = [
        (
            f"{uid_of[int(k.split(':', 1)[0])]}:{k.split(':', 1)[1]}"
            if k.split(":", 1)[0].isdigit() and int(k.split(":", 1)[0]) in uid_of
            else k
        )
        for k in stored.get("checklist", [])
    ]
    P.update({k: v for k, v in stored.items() if k in DEFAULTS})
    this_device(P)  # mint this install's id once, here, so the save below is what persists it
    # a profile saved before sync existed counts as edited now, so a brand-new phone never overrides it.
    # A fresh default profile is never an edit: it gets rev 0 on first save and only real edits stamp it.
    save_profile(db, touch=bool(row) and kv_get(db, "profile_rev") is None)


def save_profile(db, touch=True):
    """touch=True marks a real edit that should sync; loading or updating local-only keys passes False."""
    db.execute("INSERT OR REPLACE INTO kv VALUES('profile', ?)", (json.dumps(P),))
    db.execute("INSERT OR REPLACE INTO kv VALUES('saved_at', ?)", (dt.datetime.now().isoformat(timespec="seconds"),))
    if touch:
        db.execute("INSERT OR REPLACE INTO kv VALUES('profile_updated', ?)", (str(now_ms()),))
        db.execute("INSERT OR REPLACE INTO kv VALUES('profile_rev', ?)", (str(bump_rev(db)),))
    else:
        db.execute("INSERT OR IGNORE INTO kv VALUES('profile_updated', '0')")
        db.execute("INSERT OR IGNORE INTO kv VALUES('profile_rev', '0')")
    db.commit()


def readiness(rows, tsb, issues=()):
    """rows: wellness rows newest first; issues: health issues active today."""
    if not rows and not issues:
        return None, ["Log a morning check-in on the Wellness page to get a readiness score."]
    if not rows:
        rows = [
            dict(
                date=dt.date.today().isoformat(),
                rhr=None,
                hrv=None,
                sleep_h=None,
                soreness=None,
                stress=None,
                fatigue=None,
            )
        ]
    t, prev = rows[0], rows[1:8]
    avg = lambda k: (lambda v: sum(v) / len(v) if v else None)([r[k] for r in prev if r[k]])
    score, notes = 100, []
    ra, ha = avg("rhr"), avg("hrv")
    if t["rhr"] and ra and t["rhr"] > ra + 5:
        score -= 20
        notes.append(f"Resting HR {t['rhr']:.0f} vs {ra:.0f} avg - possible fatigue/illness")
    if t["hrv"] and ha and t["hrv"] < ha * 0.9:
        score -= 20
        notes.append(f"HRV {t['hrv']:.0f} below {ha:.0f} avg")
    if t["sleep_h"]:
        if t["sleep_h"] < 6:
            score -= 15
            notes.append("Short sleep")
        elif t["sleep_h"] < 7:
            score -= 5
    score -= ((t["soreness"] or 1) - 1) * 6 + ((t["stress"] or 1) - 1) * 4 + ((t["fatigue"] or 1) - 1) * 6
    for i in issues:
        score -= i["severity"] * 8
        notes.append(f"{i['name']} ({SEVERITY[i['severity']].lower()})")
    if tsb < -30:
        score -= 15
        notes.append("Training stress balance very negative")
    score = max(0, score)
    advice = (
        "Green light - hit today's key session."
        if score >= 80
        else (
            "Train, but cap intensity at tempo; swap intervals to Z2 if legs feel flat."
            if score >= 60
            else "Easy day or rest. Recovery is where fitness is banked."
        )
    )
    when = "" if t["date"] == dt.date.today().isoformat() else f" (from {t['date']})"
    return score, [f"Readiness {score}/100{when}: {advice}"] + notes


# ---------------------------------------------------------------- desktop API (called from ui.html via pywebview)


def _locked(fn):
    def w(self, *a):
        with self._lock:
            return fn(self, *a)

    w.__name__ = fn.__name__
    return w


def _f(v, fmt="{:.0f}"):
    return fmt.format(v) if v else ""


def not_done(sessions, rows, day):
    """Planned sessions for `day` that no logged workout covers yet. Each logged workout ticks off one planned
    session of the same sport (Brick counts as Bike), so two planned runs and one logged run leave one open."""
    fam = lambda sp: SPORT_FAMILY.get(sp, sp)
    logged = [fam(w["sport"]) for w in rows if w["date"] == day.isoformat()]
    out = []
    for s in sessions:
        if s[1] not in ("Race", "Rest") and fam(s[1]) in logged:
            logged.remove(fam(s[1]))
        else:
            out.append(s)
    return out


def sess_ref(s):
    """A planned session points at a race (int id) or at a session the athlete scheduled ("s:uid")."""
    return dict(race_id=s[5] if isinstance(s[5], int) else None, sched=s[5][2:] if isinstance(s[5], str) else None)


def _nice_date(d):
    year = f", {d.year}" if (dt.date.today() - d).days > 365 else ""  # a date over a year back needs its year
    return f"{d:%a, %b} {d.day}{year}"


class Api:
    """Every public method is callable from JS as window.pywebview.api.<name>(...)."""

    def __init__(self, db_path=DB_PATH):
        self._path = db_path
        self._lock = threading.RLock()
        self._undo, self._undo_seq = {}, 0
        self._anchor_key = None
        self._wx = None  # latest forecast (Open-Meteo hourly, last ~3 months + next 10 days), handed over by the UI
        self._hub = None
        self._window = None
        self._backup = backup_db(db_path) if db_path != ":memory:" else None
        self._db = open_db(db_path)
        with self._lock:
            load_profile(self._db)

    # ---- internals
    def _workouts(self):
        rows = self._db.execute("SELECT * FROM workouts ORDER BY date DESC, id DESC").fetchall()
        key = (tuple((w["id"], w["date"], w["dur_s"], w["dist_km"], w["sport"]) for w in rows), P["recent_race_km"])
        if key != self._anchor_key:  # predictions read the run anchor, so it has to follow the log
            self._anchor_key = key
            _RUN_ANCHORS[:] = best_run_anchors(_efforts(rows, self._races(forecast=False), P)[0])
        return rows

    def _wellness(self):
        return self._db.execute("SELECT * FROM wellness ORDER BY date DESC").fetchall()

    def _issues(self):
        return [issue_from_row(r) for r in self._db.execute("SELECT * FROM issues ORDER BY start DESC, id DESC")]

    def _gear(self):
        return [gear_from_row(r) for r in self._db.execute("SELECT * FROM gear ORDER BY active DESC, name")]

    def _gear_totals(self):
        """dist_km/dur_s accrued per gear item, summed straight off the workout log."""
        rows = self._db.execute(
            "SELECT gear_id, SUM(dist_km) dist_km, SUM(dur_s) dur_s FROM workouts "
            "WHERE gear_id IS NOT NULL GROUP BY gear_id"
        )
        return {r["gear_id"]: (r["dist_km"] or 0, r["dur_s"] or 0) for r in rows}

    def _default_gear_id(self, sport):
        return next((g["id"] for g in self._gear() if g["active"] and g["is_default"] and sport in g["sports"]), None)

    def _resolve_gear_id(self, sport, raw):
        """"" (no override) follows the default for the sport; "none" opts out of auto-assignment entirely."""
        if raw in (None, ""):
            return self._default_gear_id(sport)
        if raw == "none":
            return None
        try:
            return int(raw)
        except (TypeError, ValueError):
            return self._default_gear_id(sport)

    def _races(self, forecast=True):
        rs = [race_from_row(r) for r in self._db.execute("SELECT * FROM races ORDER BY date, id")]
        for r in (
            rs if forecast and self._wx else []
        ):  # the forecast replaces the typed-in temperature once it covers race day
            start = at(dt.date.fromisoformat(r["date"]), r["start"])
            w = wx_during(self._wx, start, start + dt.timedelta(seconds=min(r["goal_s"] or 10800, 21600)))
            if w and w["dew"] is not None:
                r.update(temp_c=w["temp_max"], dew_c=w["dew"], wx=w)
        return rs

    def _series(self):
        daily = {}
        for w in self._workouts():
            d = dt.date.fromisoformat(w["date"])
            daily[d] = daily.get(d, 0) + (w["tss"] or 0)
        today = dt.date.today()
        return pmc(daily, min(list(daily) + [today - dt.timedelta(days=120)]), today)

    def _scheduled(self):
        return [sched_from_row(r) for r in self._db.execute("SELECT * FROM scheduled ORDER BY date, time")]

    def _plan(self, series=None):
        series = series or self._series()
        return build_plan(P, self._races(), ctl=series[-1][1], issues=self._issues(), scheduled=self._scheduled())

    def _projection(self, target, weeks, series):
        """CTL/ATL from today to the target's race morning, following the plan."""
        today = dt.date.today()
        if not target:
            return []
        end = dt.date.fromisoformat(target["date"]) - ONE  # race morning: exclude the race's own TSS
        planned = {}
        for w in weeks:
            for s in w["sessions"]:
                if s[0] > today:
                    planned[s[0]] = planned.get(s[0], 0) + s[3]
        return pmc(planned, today + ONE, end, series[-1][1], series[-1][2]) if end > today else []

    def _save(self):
        save_profile(self._db)

    def _sports(self):
        return [s for s in ALL_SPORTS if s in P["sports"]] or ["Run"]

    def _wrow(self, w):
        d, dur, s = w["dist_km"] or 0, w["dur_s"] or 0, w["sport"]
        if d and s == "Swim":
            dist, pace = swim_dist_ui(d), fd("swim", dur / (d * 10))
        elif d:
            dist = fd("dist", d)
            pace = fd("pace", dur / d) if s in ("Run", "Hike", "Walk") else speed_ui(d / (dur / 3600)) if dur else ""
        else:
            dist = pace = ""
        h, r = divmod(int(round(dur)), 3600)
        cond, adj = ("Indoors", "") if w["indoor"] else ("", "")
        if w["wx_temp"] is not None and not w["indoor"]:
            cond = fd("temp", w["wx_temp"]) + (f" · dew {fd('temp', w['wx_dew'])}" if w["wx_dew"] is not None else "")
            pct = heat_slowdown(w["wx_temp"], w["wx_dew"])[0] if w["wx_dew"] is not None else 0
            if d and dur and s in ("Run", "Hike", "Walk") and pct >= 1:
                adj = fd("pace", dur / d / (1 + pct / 100))  # what the effort is worth in cool weather
        splits = json.loads(w["splits"]) if w["splits"] else None
        if splits:
            for sp in splits:
                sp["pace"] = (
                    fd("swim", sp["dur_s"] / (sp["dist_m"] / 100))
                    if s == "Swim"
                    else fd("pace", sp["dur_s"] / (sp["dist_m"] / 1000))
                )
        return dict(
            id=w["id"],
            date=w["date"],
            nice=_nice_date(dt.date.fromisoformat(w["date"])),
            sport=s,
            cond=cond,
            adj=adj,
            dur=hms(dur),
            dist=dist,
            pace=pace,
            hr=_f(w["avg_hr"]),
            w=_f(w["avg_w"]),
            rpe=_f(w["rpe"]),
            tss=_f(w["tss"]),
            kcal=_f(w["kcal"]),
            notes=w["notes"] or "",
            splits=splits,
            edit=dict(
                date=w["date"],
                sport=s,
                h=h,
                m=r // 60,
                s=r % 60,
                dist=leg_dist_ui(s, d) if d else "",
                rpe=_f(w["rpe"]),
                hr=_f(w["avg_hr"]),
                w=_f(w["avg_w"]),
                notes=w["notes"] or "",
                indoor=bool(w["indoor"]),
                gear_id=w["gear_id"] or "",
            ),
        )

    def _parse_workout(self, f):
        sport = f.get("sport") or "Run"
        date = dt.date.fromisoformat(f.get("date") or "").isoformat()
        dur = float(f.get("h") or 0) * 3600 + float(f.get("m") or 0) * 60 + float(f.get("s") or 0)
        if dur <= 0:
            raise ValueError("Enter a duration")
        dist = leg_dist_from(sport, f.get("dist") or 0)
        g = lambda k: float(f[k]) if str(f.get(k) or "").strip() else None
        rpe, hr, w = g("rpe"), g("hr"), g("w")
        tss = estimate_tss(P, sport, dur, dist, rpe, hr, w)
        kcal = estimate_kcal(P, sport, dur, dist, w, tss)
        return (date, sport, dur, dist, rpe, hr, w, tss, kcal, (f.get("notes") or "").strip())

    def _race_summary(self, r, ctl, target_id):
        today = dt.date.today()
        d = dt.date.fromisoformat(r["date"])
        pr = predict(P, r, ctl)
        return dict(
            id=r["id"],
            name=r["name"],
            date=r["date"],
            nice=f"{d:%a, %b} {d.day}, {d.year}",
            short=f"{d:%b} {d.day}",
            days=(d - today).days,
            past=d < today,
            priority=r["priority"],
            kind=race_kind(r),
            preset=r["preset"],
            target=r["id"] == target_id,
            dist=" · ".join(leg_label(l["sport"], l["km"]) for l in r["legs"]),
            sports=[l["sport"] for l in r["legs"]],
            predicted=hms(pr["total"]) if pr["total"] else "",
            modelled=pr["modelled"],
            goal=hms(r["goal_s"]) if r["goal_s"] else "",
            result=hms(r["result_s"]) if r["result_s"] else "",
        )

    # ---- shell
    @_locked
    def boot(self):
        races = self._races()
        today = dt.date.today()
        nxt = next((r for r in races if dt.date.fromisoformat(r["date"]) >= today), None)
        target = pick_target(P, races, today)
        return dict(
            name=P["name"],
            theme=P.get("theme", "light"),
            units=P["units"],
            version=VERSION,
            dist_unit=unit("dist"),
            swim_unit="yd" if imp() else "m",
            weight_unit=unit("weight"),
            vol_unit=unit("vol"),
            elev_unit=unit("elev"),
            temp_unit=unit("temp"),
            sports=self._sports(),
            all_sports=ALL_SPORTS,
            leg_sports=LEG_SPORTS,
            run_thr_pace=P["run_thr_pace"],
            next_race=dict(name=nxt["name"], date=nxt["date"], priority=nxt["priority"]) if nxt else None,
            target=dict(name=target["name"], date=target["date"]) if target else None,
            plan_start=P["plan_start"],
            today=today.isoformat(),
            setup_done=P.get("setup_done", False),
            paired=bool(P["sync_host"]),
            sync_host=P["sync_host"],
            sync_last=P["sync_last"],
            loc=dict(place=P["home_place"], lat=P["home_lat"], lon=P["home_lon"]) if P["home_place"] else None,
        )

    @_locked
    def set_theme(self, theme):
        P["theme"] = theme
        self._save()

    # ---- dashboard
    @_locked
    def dashboard(self):
        today = dt.date.today()
        series = self._series()
        _, ctl, atl, tsb = series[-1]
        target, weeks = self._plan(series)
        proj = self._projection(target, weeks, series)
        races = self._races()
        upcoming = [r for r in races if dt.date.fromisoformat(r["date"]) >= today]
        nxt = upcoming[0] if upcoming else None
        pr = predict(P, nxt, proj[-1][1] if proj and nxt is target else ctl) if nxt else None
        hist = series[-90:]
        both = hist + proj[:240]
        rows = self._workouts()
        mon = today - ONE * today.weekday()
        present = [s for s in ALL_SPORTS if s in P["sports"] or any(w["sport"] == s for w in rows[:400])]
        groups = [s for s in present if s not in ("Mobility",)][:6] or ["Run"]
        grp = lambda s: s if s in groups else "Other"
        if "Other" not in groups and any(grp(w["sport"]) == "Other" for w in rows[:400]):
            groups.append("Other")
        wlabels, wdata = [], {k: [] for k in groups}
        for i in range(11, -1, -1):
            ws = mon - dt.timedelta(weeks=i)
            st = dict.fromkeys(wdata, 0.0)
            for w in rows:
                if ws.isoformat() <= w["date"] < (ws + 7 * ONE).isoformat() and grp(w["sport"]) in st:
                    st[grp(w["sport"])] += (w["dur_s"] or 0) / 3600
            wlabels.append(f"{ws:%b} {ws.day}")
            for k in wdata:
                wdata[k].append(round(st[k], 2))
        split = dict.fromkeys(groups, 0.0)
        for w in rows:
            if (today - dt.date.fromisoformat(w["date"])).days < 28 and grp(w["sport"]) in split:
                split[grp(w["sport"])] += (w["dur_s"] or 0) / 3600
        todays = [s for w in weeks for s in w["sessions"] if s[0] == today]
        plan_h = sum(s[2] for w in weeks for s in w["sessions"] if mon <= s[0] < mon + 7 * ONE and s[1] != "Race")
        done_h = sum(w["dur_s"] or 0 for w in rows if mon.isoformat() <= w["date"] < (mon + 7 * ONE).isoformat())
        phase = next((w["phase"] for w in weeks if w["start"] <= today < w["start"] + 7 * ONE), None)
        active = active_on(self._issues(), today)
        score, notes = readiness(self._wellness(), tsb, active)
        state = load_state(rows, series, P, today)
        advice = daily_advice(state, score, active, today)
        open_today = not_done(todays, rows, today)
        coached = adapt_for_load(P, open_today, advice, state)
        nut = daily_nutrition(
            P,
            [(s[1], s[2], estimate_kcal(P, s[1], s[2], tss=s[3])) for s in todays if s[1] not in ("Race", "Rest")],
            P["goal"],
        )
        ramp = ctl - series[-8][1] if len(series) > 8 else 0
        # ACWR (state["acwr"]) is the sharper read on the same "loading too fast" risk; once it has already
        # flagged the week, the coarser CTL-ramp check stays quiet instead of raising a second, redundant alarm.
        ramp_warn = ramp > 8 and (state["acwr"] is None or state["acwr"] < 1.35)
        labels = [d.isoformat() for d, *_ in both]
        markers = [
            dict(i=labels.index(r["date"]), name=r["name"], p=r["priority"]) for r in races if r["date"] in labels
        ]
        return dict(
            name=P["name"],
            ctl=round(ctl),
            atl=round(atl),
            tsb=round(tsb),
            form=form_label(tsb),
            ramp=round(ramp, 1),
            ramp_warn=ramp_warn,
            next_race=(
                dict(
                    id=nxt["id"],
                    name=nxt["name"],
                    priority=nxt["priority"],
                    date=f"{dt.date.fromisoformat(nxt['date']):%b} {dt.date.fromisoformat(nxt['date']).day}",
                    days=(dt.date.fromisoformat(nxt["date"]) - today).days,
                    predicted=hms(pr["total"]) if pr and pr["total"] else "—",
                    splits=[
                        dict(sport=s["sport"], time=hms(s["secs"]))
                        for s in pr["segs"]
                        if s["kind"] == "leg" and s["secs"]
                    ],
                )
                if nxt
                else None
            ),
            more_races=max(0, len(upcoming) - 1),
            target=dict(name=target["name"]) if target else None,
            ctl_race=round(proj[-1][1]) if proj else None,
            tsb_race=round(proj[-1][3]) if proj else None,
            form_race=form_label(proj[-1][3]) if proj else "",
            spark_ctl=[round(x[1], 1) for x in series[-42:]],
            spark_tsb=[round(x[3], 1) for x in series[-42:]],
            spark_atl=[round(x[2], 1) for x in series[-42:]],
            pmc=dict(
                labels=labels,
                split=len(hist),
                ctl=[round(x[1], 1) for x in both],
                atl=[round(x[2], 1) for x in both],
                tsb=[round(x[3], 1) for x in both],
                markers=markers,
            ),
            weekly=dict(labels=wlabels, series=wdata),
            sport_split={k: round(v, 1) for k, v in split.items()},
            today=[
                dict(
                    sport=s[1],
                    dur=hms(s[2]),
                    tss=round(s[3]),
                    desc=s[4],
                    **sess_ref(s),
                    k=todays.index(open_today[i]) if i < len(open_today) else 0,
                    wx=self._wx_line(s),
                    fuel=fuel_session(P, s[1], s[2]),
                )
                for i, s in enumerate(coached)
            ],
            advice=dict(
                **advice,
                trained_today=state["trained_today"],
                recovery_h=state["recovery"]["hours"],
                changed=[s[1] for s in open_today] != [s[1] for s in coached]
                or any(abs(a[2] - b[2]) > 60 for a, b in zip(open_today, coached)),
            ),
            status=training_status(
                rows, series, state, (dt.date.fromisoformat(nxt["date"]) - today).days if nxt else None
            ),
            done_today=[self._wrow(w) for w in rows if w["date"] == today.isoformat()],
            phase=phase,
            week_done=round(done_h / 3600, 1),
            week_plan=round(plan_h / 3600, 1),
            readiness=score,
            readiness_notes=notes,
            fuel=dict(
                kcal=round(nut["kcal"]), carbs=round(nut["carbs"]), protein=round(nut["protein"]), fat=round(nut["fat"])
            ),
            recent=[self._wrow(w) for w in rows[:6]],
            habits=[
                dict(uid=h["uid"], name=h["name"], done=today.isoformat() in self._done_dates(h["uid"]))
                for h in self._habits()
                if today.weekday() in json.loads(h["days"])
            ],
            quote=self._quote_for(today),
            issues=[
                dict(
                    id=i["id"],
                    name=i["name"],
                    kind=i["kind"],
                    severity=i["severity"],
                    sev_label=SEVERITY[i["severity"]],
                    days=(today - dt.date.fromisoformat(i["start"])).days + 1,
                    sports=i["sports"],
                )
                for i in active
            ],
        )

    # ---- updates
    def update_check(self):
        """Ask GitHub whether there is a newer release. Reads only; not @_locked, it waits on the network."""
        return check_for_update()

    def update_install(self, url, size=None):
        """Download and swap in a newer build. Only ever called from a button the athlete pressed."""
        return install_update(url, size)

    # ---- coach: today's verdict and the evidence behind it
    @_locked
    def coach(self):
        today = dt.date.today()
        rows, series = self._workouts(), self._series()
        active = active_on(self._issues(), today)
        score, notes = readiness(self._wellness(), series[-1][3], active)
        state = load_state(rows, series, P, today)
        advice = daily_advice(state, score, active, today)
        _, weeks = self._plan(series)
        todays = [s for w in weeks for s in w["sessions"] if s[0] == today]
        open_today = not_done(todays, rows, today)
        coached = adapt_for_load(P, open_today, advice, state)
        races = [r for r in self._races(forecast=False) if r["date"] >= today.isoformat()]
        drift = threshold_drift(P, records(rows, self._races(forecast=False), P)) if rows else []
        return dict(
            advice=dict(**advice, trained_today=state["trained_today"]),
            planned=[dict(sport=s[1], dur=hms(s[2]), tss=round(s[3]), desc=s[4]) for s in open_today],
            coached=[dict(sport=s[1], dur=hms(s[2]), tss=round(s[3]), desc=s[4]) for s in coached],
            readiness=score,
            readiness_notes=notes,
            signals=fatigue_signals(self._wellness(), series, today),
            status=training_status(
                rows, series, state, (dt.date.fromisoformat(races[0]["date"]) - today).days if races else None
            ),
            mix=intensity_mix(rows, today),
            drift=drift,
            load=dict(
                acwr=state["acwr"],
                monotony=state["monotony"],
                strain=state["strain"],
                week_tss=state["week_tss"],
                last48=state["last48"],
                last72=state["last72"],
                hard_streak=state["hard_streak"],
                since_rest=state["since_rest"],
                tsb=state["tsb"],
                ctl=state["ctl"],
            ),
            recovery=state["recovery"],
            done_today=[self._wrow(w) for w in rows if w["date"] == today.isoformat()],
        )

    @_locked
    def apply_drift(self, key, value):
        """Accept a suggested threshold change. Only ever on the athlete's say-so."""
        if key not in ("run_thr_pace", "ftp", "css") or not float(value) > 0:
            return dict(ok=False, error="Unknown setting")
        P[key] = float(value)
        self._save()
        return dict(ok=True)

    # ---- log
    @_locked
    def workouts(self):
        rows = self._workouts()
        today = dt.date.today()
        mon = today - ONE * today.weekday()
        wk = [w for w in rows if w["date"] >= mon.isoformat()]
        d28 = [w for w in rows if (today - dt.date.fromisoformat(w["date"])).days < 28]
        return dict(
            rows=[self._wrow(w) for w in rows],
            sports=[s for s in ALL_SPORTS if s in P["sports"] or any(w["sport"] == s for w in rows)],
            gear=[dict(id=g["id"], name=g["name"], sports=g["sports"]) for g in self._gear() if g["active"]],
            stats=dict(
                week_h=round(sum(w["dur_s"] or 0 for w in wk) / 3600, 1),
                week_n=len(wk),
                d28_h=round(sum(w["dur_s"] or 0 for w in d28) / 3600, 1),
                d28_tss=round(sum(w["tss"] or 0 for w in d28) / 4),
                total=len(rows),
                total_h=round(sum(w["dur_s"] or 0 for w in rows) / 3600),
            ),
        )

    @_locked
    def preview_workout(self, f):
        try:
            date, sport, dur, dist, rpe, hr, w, tss, kcal, _ = self._parse_workout(f)
        except (ValueError, TypeError):
            return None
        pace = ""
        if dist and sport == "Swim":
            pace = fd("swim", dur / (dist * 10))
        elif dist and sport in ("Run", "Hike", "Walk"):
            pace = fd("pace", dur / dist)
        elif dist:
            pace = speed_ui(dist / (dur / 3600))
        src = (
            "power"
            if w and sport in ("Bike", "Brick")
            else (
                "pace"
                if dist and sport in ("Run", "Swim")
                else "heart rate" if hr else "RPE" if rpe else "default effort"
            )
        )
        return dict(tss=round(tss), kcal=round(kcal), dur=hms(dur), pace=pace, src=src)

    @_locked
    def save_workout(self, f):
        try:
            rec = self._parse_workout(f)
        except (ValueError, TypeError) as e:
            return dict(ok=False, error=str(e) or "Check the form")
        indoor = 1 if f.get("indoor") not in (None, "", False, "false", "0") else 0
        gear_id = self._resolve_gear_id(rec[1], f.get("gear_id"))
        if f.get("id"):
            # GPS splits describe the session that was recorded. Correcting a note or a heart rate leaves them
            # true; changing how far or how long it was does not, and stale splits would go on feeding best
            # efforts for a workout that no longer exists.
            was = self._db.execute("SELECT dur_s, dist_km FROM workouts WHERE id=?", (int(f["id"]),)).fetchone()
            if was and leg_dist_ui(rec[1], was["dist_km"] or 0) == str(f.get("dist") or "").strip():
                # the box still holds the number we put in it, rounded for display. Re-parsing that would shave
                # a few metres off every time the notes were touched, so keep what was actually recorded.
                rec = rec[:3] + (was["dist_km"],) + rec[4:]
            reshaped = was and (abs((was["dur_s"] or 0) - rec[2]) > 1 or abs((was["dist_km"] or 0) - rec[3]) > 0.005)
            self._db.execute(
                "UPDATE workouts SET date=?,sport=?,dur_s=?,dist_km=?,rpe=?,avg_hr=?,avg_w=?,tss=?,kcal=?,"
                "notes=?,indoor=?,gear_id=?,wx_temp=NULL,wx_dew=NULL,wx_code=NULL"
                + (",splits=NULL" if reshaped else "")
                + " WHERE id=?",
                rec + (indoor, gear_id, int(f["id"])),
            )
        else:
            self._db.execute(
                "INSERT INTO workouts(date,sport,dur_s,dist_km,rpe,avg_hr,avg_w,tss,kcal,notes,indoor,gear_id) "
                "VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",
                rec + (indoor, gear_id),
            )
        if self._wx:
            self._stamp_weather()
        self._db.commit()
        return dict(ok=True)

    @_locked
    def save_live_workout(self, f):
        """Finish of the phone's live-tracking screen: dur_s/dist_km/avg_hr/splits already computed natively
        (GPS + HealthKit), unlike save_workout's hand-typed h/m/s form."""
        sport = f.get("sport") or "Run"
        date = dt.date.fromisoformat(f.get("date") or dt.date.today().isoformat()).isoformat()
        dur, dist, hr = float(f.get("dur_s") or 0), float(f.get("dist_km") or 0), f.get("avg_hr")
        if dur <= 0:
            return dict(ok=False, error="No recorded time")
        tss = estimate_tss(P, sport, dur, dist, None, hr, None)
        kcal = estimate_kcal(P, sport, dur, dist, None, tss)
        splits = json.dumps(f["splits"]) if f.get("splits") else None
        indoor = 1 if f.get("indoor") not in (None, "", False, "false", "0") else 0
        gear_id = self._resolve_gear_id(sport, f.get("gear_id"))
        try:  # the native side stamps UTC ("...Z"); everything downstream compares against naive local times
            start = _stamp(_local(dt.datetime.fromisoformat(str(f["start"]).strip()))) if f.get("start") else None
        except ValueError:
            start = None
        self._db.execute(
            "INSERT INTO workouts(date,start,sport,dur_s,dist_km,rpe,avg_hr,avg_w,tss,kcal,notes,indoor,splits"
            ",gear_id) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                date,
                start,
                sport,
                dur,
                dist,
                None,
                hr,
                None,
                tss,
                kcal,
                (f.get("notes") or "").strip(),
                indoor,
                splits,
                gear_id,
            ),
        )
        if self._wx and not indoor:
            self._stamp_weather()
        self._db.commit()
        return dict(ok=True)

    @_locked
    def delete_workouts(self, ids):
        return self._take("workouts", "id", [int(i) for i in ids])

    # ---- undo: deletes stash the removed rows so the UI can put them back
    def _take(self, table, key, values, profile=None):
        rows = [dict(r) for v in values for r in self._db.execute(f"SELECT * FROM {table} WHERE {key}=?", (v,))]
        self._db.executemany(f"DELETE FROM {table} WHERE {key}=?", [(v,) for v in values])
        self._db.commit()
        self._undo_seq += 1
        self._undo[self._undo_seq] = (table, rows, profile)
        for old in sorted(self._undo)[
            :-20
        ]:  # ponytail: last 20 deletes per session; persist if undo must survive restarts
            del self._undo[old]
        return dict(ok=True, undo=self._undo_seq, n=len(rows))

    @_locked
    def undo(self, token):
        entry = self._undo.pop(int(token), None)
        if not entry:
            return dict(ok=False, error="That can no longer be undone")
        table, rows, profile = entry
        with self._db:
            for r in rows:
                cols = ",".join(f'"{c}"' for c in r)
                self._db.execute(
                    f"INSERT OR REPLACE INTO {table}({cols}) VALUES({','.join('?' * len(r))})", list(r.values())
                )
        if profile:
            P.update(profile)
            self._save()
        return dict(ok=True, n=len(rows))

    def import_files(self):
        import webview

        paths = self._window.create_file_dialog(
            webview.FileDialog.OPEN,
            allow_multiple=True,
            file_types=("Activity files (*.csv;*.tcx;*.gpx)", "Strava export (*.csv)", "All files (*.*)"),
        )
        with self._lock:
            return dict(self._import_paths(paths or []), cancelled=not paths)

    def _import_paths(self, paths):
        acts, bad = [], []
        for p in paths:
            try:
                if p.lower().endswith(".csv"):
                    rows, n_bad = parse_strava_csv(p)
                    acts += rows
                    if n_bad:
                        bad.append(f"{os.path.basename(p)}: {n_bad} unreadable row(s) skipped")
                else:
                    acts.append(parse_activity(p))
            except Exception as e:  # one bad file shouldn't stop the batch
                bad.append(f"{os.path.basename(p)}: {e}")
        added, dups = self._import_activities(acts)
        return dict(ok=added, skipped=len(dups), dups=dups[:8], bad=bad)

    def _import_activities(self, acts):
        """Insert activities, skipping any that duplicate an existing workout (or one earlier in this batch)."""
        added, dups = 0, []
        for a in sorted(acts, key=lambda x: x.get("start") or x["date"]):
            same_day = [
                dict(r)
                for r in self._db.execute(
                    "SELECT sport, date, start, dur_s, dist_km FROM workouts WHERE date=?", (a["date"],)
                )
            ]
            if any(is_duplicate(a, b) for b in same_day):
                dups.append(
                    f"{a['date']} {a['sport']} {leg_label(a['sport'], a['dist_km']) if a['dist_km'] else hms(a['dur_s'])}"
                )
                continue
            tss = estimate_tss(P, a["sport"], a["dur_s"], a["dist_km"], None, a["avg_hr"], a["avg_w"])
            kcal = estimate_kcal(P, a["sport"], a["dur_s"], a["dist_km"], a["avg_w"], tss)
            splits = self._take_watch_splits(a.get("start")) if a.get("start") else None
            self._db.execute(
                "INSERT INTO workouts(date,start,sport,dur_s,dist_km,rpe,avg_hr,avg_w,tss,kcal,notes,indoor,splits) "
                "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (
                    a["date"],
                    a.get("start"),
                    a["sport"],
                    a["dur_s"],
                    a["dist_km"],
                    None,
                    a["avg_hr"],
                    a["avg_w"],
                    tss,
                    kcal,
                    a.get("notes") or "Imported",
                    1 if a.get("indoor") else 0,
                    splits,
                ),
            )
            added += 1
        self._db.commit()
        return added, dups

    def _take_watch_splits(self, start):
        """Consume a splits payload the watch delivered for this workout's start time, if one arrived."""
        row = self._db.execute("SELECT v FROM kv WHERE k=?", (f"wsplits:{start}",)).fetchone()
        if not row:
            return None
        self._db.execute("DELETE FROM kv WHERE k=?", (f"wsplits:{start}",))
        return row[0]

    @_locked
    def save_watch_splits(self, start, splits):
        """The watch app delivers splits (via WatchConnectivity) keyed by the workout's start time. The matching
        workout usually arrives later through the normal Health import, so stash it until then; but if that
        workout is already here (Health synced first), attach it immediately."""
        row = self._db.execute("SELECT id FROM workouts WHERE start=?", (start,)).fetchone()
        if row:
            self._db.execute("UPDATE workouts SET splits=? WHERE id=?", (json.dumps(splits), row[0]))
            self._db.commit()
        else:
            self._db.execute("INSERT OR REPLACE INTO kv VALUES(?, ?)", (f"wsplits:{start}", json.dumps(splits)))
            self._db.commit()
        return dict(ok=True)

    # ---- watch folder (desktop): Garmin Express/Wahoo drop .fit/.tcx/.gpx into a folder on the PC
    @_locked
    def watchfolder_state(self):
        return dict(on=P["watchfolder_on"], path=P["watchfolder_path"], last=P["watchfolder_last"])

    def watchfolder_choose(self):
        import webview

        paths = self._window.create_file_dialog(webview.FileDialog.FOLDER)
        if not paths:
            return dict(cancelled=True)
        with self._lock:
            P["watchfolder_path"] = paths[0] if isinstance(paths, (list, tuple)) else paths
            P["watchfolder_on"] = True
            self._save()
            return dict(self.watchfolder_scan(), cancelled=False)

    @_locked
    def watchfolder_enable(self, on):
        P["watchfolder_on"] = bool(on)
        self._save()
        return dict(ok=True)

    @_locked
    def watchfolder_scan(self):
        """Pick up new .gpx/.tcx/.csv files a watch-sync tool dropped in the watched folder. There's no separate
        "already seen" ledger: every file in the folder is re-parsed on each scan and handed to the same
        is_duplicate check manual import uses, so a file imported last time is silently skipped, not re-added.
        That trades a little repeated parsing for one duplicate mechanism instead of two.
        .fit isn't a format parse_activity reads (see its docstring: export TCX from Garmin Connect/Strava
        instead), so .fit files are counted and reported rather than silently ignored."""
        path = P["watchfolder_path"]
        if not P["watchfolder_on"] or not path:
            return dict(ok=0, skipped=0, dups=[], bad=[], disabled=True)
        try:
            names = os.listdir(path)
        except OSError as e:
            return dict(ok=0, skipped=0, dups=[], bad=[f"Watch folder unavailable: {e.strerror or e}"], disabled=False)
        paths = [os.path.join(path, n) for n in names if n.lower().endswith((".gpx", ".tcx", ".csv"))]
        n_fit = sum(1 for n in names if n.lower().endswith(".fit"))
        result = self._import_paths(paths)
        if n_fit:
            result["bad"] = result["bad"] + [
                f"{n_fit} .fit file(s) skipped — export as TCX from Garmin Connect/Strava"
            ]
        P["watchfolder_last"] = dt.datetime.now().isoformat(timespec="seconds")
        self._save()
        return dict(result, disabled=False)

    def _save_dialog(self, name, types):
        import webview

        path = self._window.create_file_dialog(webview.FileDialog.SAVE, save_filename=name, file_types=types)
        return (path[0] if path else None) if isinstance(path, (list, tuple)) else path

    def export_csv(self):
        path = self._save_dialog("workouts.csv", ("CSV (*.csv)",))
        if not path:
            return dict(cancelled=True)
        out = self.export_csv_text()
        with open(path, "w", newline="", encoding="utf-8") as fh:
            fh.write(out["text"])
        return dict(n=out["n"], path=path)

    @_locked
    def export_csv_text(self):
        import io

        rows = self._workouts()
        buf = io.StringIO()
        wr = csv.writer(buf)
        wr.writerow(rows[0].keys() if rows else ["date"])
        wr.writerows([tuple(r) for r in rows])
        return dict(n=len(rows), text=buf.getvalue())

    # ---- plan
    @_locked
    def plan(self):
        target, weeks = self._plan()
        rows = self._workouts()
        done_by_day, sports_by_day = {}, {}
        for w in rows:
            done_by_day[w["date"]] = done_by_day.get(w["date"], 0) + (w["dur_s"] or 0)
            sports_by_day.setdefault(w["date"], set()).add(w["sport"])
        today = dt.date.today()
        out = []
        for i, w in enumerate(weeks):
            end = w["start"] + 6 * ONE
            dh = sum(v for d, v in done_by_day.items() if w["start"].isoformat() <= d <= end.isoformat())
            days = []
            for k in range(7):
                d = w["start"] + k * ONE
                sess = [
                    dict(
                        sport=s[1],
                        dur=hms(s[2]),
                        dur_s=s[2],
                        tss=round(s[3]),
                        desc=s[4],
                        **sess_ref(s),
                        done=s[1] in sports_by_day.get(d.isoformat(), ()),
                        fuel=fuel_session(P, s[1], s[2]),
                    )
                    for s in w["sessions"]
                    if s[0] == d
                ]
                days.append(
                    dict(date=d.isoformat(), dow=f"{d:%a}", day=d.day, today=d == today, past=d < today, sessions=sess)
                )
            out.append(
                dict(
                    i=i,
                    start=w["start"].isoformat(),
                    label=f"{w['start']:%b} {w['start'].day}",
                    range=f"{w['start']:%b} {w['start'].day} – {end:%b} {end.day}",
                    phase=w["phase"],
                    hours=round(w["hours"], 1),
                    done=round(dh / 3600, 1),
                    races=[s[4].split(" (")[0] for s in w["sessions"] if s[1] == "Race"],
                    tss=round(sum(s[3] for s in w["sessions"])),
                    focus=PHASE_FOCUS[w["phase"]],
                    current=w["start"] <= today <= end,
                    past=end < today,
                    days=days,
                )
            )
        races = [r for r in self._races() if dt.date.fromisoformat(r["date"]) >= today]
        return dict(
            weeks=out,
            target=(
                dict(id=target["id"], name=target["name"], date=target["date"], kind=race_kind(target))
                if target
                else None
            ),
            weekly=P["weekly_hours"],
            peak=P["peak_hours"],
            days=P["days_per_week"],
            long_day=DOW[int(P["long_day"])],
            recovery=P["recovery_every"],
            races=[dict(id=r["id"], name=r["name"], priority=r["priority"]) for r in races],
            plan_race=next((r["id"] for r in races if r["uid"] == P.get("plan_race")), 0),
        )

    @_locked
    def restart_plan(self):
        P["plan_start"] = dt.date.today().isoformat()
        self._save()
        return dict(ok=True)

    @_locked
    def set_plan_race(self, rid):
        P["plan_race"] = next((r["uid"] for r in self._races() if r["id"] == int(rid or 0)), "")
        self._save()
        return dict(ok=True)

    # ---- races
    @_locked
    def races(self):
        series = self._series()
        target = pick_target(P, self._races(), dt.date.today())
        rs = [self._race_summary(r, series[-1][1], target and target["id"]) for r in self._races()]
        return dict(races=rs, upcoming=[r for r in rs if not r["past"]], past=[r for r in rs if r["past"]][::-1])

    @_locked
    def race_form(self, rid=None):
        r = next((x for x in self._races(forecast=False) if x["id"] == rid), None)
        presets = [
            dict(name=n, group=g, legs=[dict(sport=s, dist=leg_dist_ui(s, km), elev="0", time="") for s, km in legs])
            for n, (g, legs) in PRESETS.items()
        ]
        if r:
            form = dict(
                id=r["id"],
                name=r["name"],
                date=r["date"],
                preset=r["preset"],
                priority=r["priority"],
                start=r["start"],
                temp=to_ui("temp", r["temp_c"]),
                t1=hms(r["t1"]),
                t2=hms(r["t2"]),
                goal=hms(r["goal_s"]) if r["goal_s"] else "",
                result=hms(r["result_s"]) if r["result_s"] else "",
                notes=r["notes"],
                legs=[
                    dict(
                        sport=l["sport"],
                        dist=leg_dist_ui(l["sport"], l["km"]),
                        elev=to_ui("elev", l.get("elev", 0)),
                        time=hms(l["secs"]) if l.get("secs") else "",
                    )
                    for l in r["legs"]
                ],
            )
        else:
            first = PRESETS["Half marathon"] if "Swim" not in P["sports"] else PRESETS["Olympic triathlon"]
            name = "Half marathon" if "Swim" not in P["sports"] else "Olympic triathlon"
            form = dict(
                id=None,
                name="",
                date=(dt.date.today() + dt.timedelta(days=84)).isoformat(),
                preset=name,
                priority="A",
                start="08:00",
                temp=to_ui("temp", 18),
                t1="3:00",
                t2="2:00",
                goal="",
                result="",
                notes="",
                legs=[dict(sport=s, dist=leg_dist_ui(s, km), elev="0", time="") for s, km in first[1]],
            )
        return dict(
            form=form,
            presets=presets,
            leg_sports=LEG_SPORTS,
            dist_unit=unit("dist"),
            swim_unit="yd" if imp() else "m",
            elev_unit=unit("elev"),
            temp_unit=unit("temp"),
        )

    @_locked
    def save_race(self, f):
        try:
            name = (f.get("name") or "").strip()
            if not name:
                raise ValueError("Give the race a name")
            date = dt.date.fromisoformat(f.get("date") or "").isoformat()
            legs = [
                dict(
                    sport=l["sport"],
                    km=leg_dist_from(l["sport"], l["dist"]),
                    elev=from_ui("elev", l.get("elev") or 0),
                    **({"secs": parse_clock(l["time"])} if (l.get("time") or "").strip() else {}),
                )
                for l in f.get("legs") or []
            ]
            if not legs or any(l["km"] <= 0 for l in legs):
                raise ValueError("Every leg needs a distance")
            if any(l.get("secs", 1) <= 0 for l in legs):
                raise ValueError("A leg time has to be a real time, like 1:22:14")
            if f.get("priority") not in ("A", "B", "C"):
                raise ValueError("Pick a priority")
            rec = (
                name,
                date,
                f.get("preset") or "Custom",
                json.dumps(legs),
                f["priority"],
                from_ui("temp", f.get("temp") or to_ui("temp", 18)),
                parse_clock(f.get("t1") or 0),
                parse_clock(f.get("t2") or 0),
                parse_clock(f["goal"]) if f.get("goal") else None,
                parse_clock(f["result"]) if f.get("result") else None,
                (f.get("notes") or "").strip(),
                "%02d:%02d" % clock(f.get("start") or "08:00"),
            )
        except (ValueError, KeyError, TypeError) as e:
            return dict(ok=False, error=str(e) if str(e) and "HH:MM" not in str(e) else "Check the race details")
        if f.get("id"):
            self._db.execute(
                "UPDATE races SET name=?,date=?,preset=?,legs=?,priority=?,temp_c=?,t1=?,t2=?,goal_s=?,"
                "result_s=?,notes=?,start=? WHERE id=?",
                rec + (int(f["id"]),),
            )
            rid = int(f["id"])
        else:
            ins = (
                "INSERT INTO races(name,date,preset,legs,priority,temp_c,t1,t2,goal_s,result_s,notes,start) "
                "VALUES(?,?,?,?,?,?,?,?,?,?,?,?)"
            )
            rid = self._db.execute(ins, rec).lastrowid
            if f.get("repeat_until"):  # a season of weekly meets in one go
                until, d = dt.date.fromisoformat(f["repeat_until"]), dt.date.fromisoformat(date) + dt.timedelta(weeks=1)
                n = 0
                while d <= until and n < 30:
                    self._db.execute(ins, (rec[0], d.isoformat(), *rec[2:]))
                    d += dt.timedelta(weeks=1)
                    n += 1
        self._db.commit()
        return dict(ok=True, id=rid)

    @_locked
    def delete_race(self, rid):
        uid = next((r["uid"] for r in self._races() if r["id"] == int(rid)), None)
        was_target = bool(uid) and P.get("plan_race") == uid
        out = self._take("races", "id", [int(rid)], profile={"plan_race": uid} if was_target else None)
        if was_target:
            P["plan_race"] = ""
            self._save()
        return out

    @_locked
    def race(self, rid):
        r = next((x for x in self._races() if x["id"] == rid), None)
        if not r:
            return None
        today = dt.date.today()
        series = self._series()
        target, weeks = self._plan(series)
        ctl_now = series[-1][1]
        race_day = dt.date.fromisoformat(r["date"])
        if target and target["id"] == r["id"]:
            proj = self._projection(target, weeks, series)
            ctl_race = proj[-1][1] if proj else ctl_now
        else:
            ctl_race = ctl_now
        pr, now = predict(P, r, ctl_race), predict(P, r, ctl_now)
        ftp, hz = P["ftp"], hr_zones(P)
        legs, pacing, total = [], [], pr["total"] or 1
        actual = [l.get("secs") for l in r["legs"]]  # what was actually run, when the splits were filled in
        li = 0
        for s in pr["segs"]:
            if s["kind"] == "trans":
                legs.append(
                    dict(leg=s["sport"], dist="", secs=s["secs"], time=hms(s["secs"]), pace="transition", sport="T")
                )
                continue
            was = actual[li] if li < len(actual) else None
            li += 1
            legs.append(
                dict(
                    leg=s["sport"],
                    sport=s["sport"],
                    dist=leg_label(s["sport"], s["km"]),
                    secs=s["secs"] or 0,
                    time=hms(s["secs"]) if s["secs"] else "—",
                    pace=s["pace"] or "no model — set a goal time",
                    actual=hms(was) if was else "",
                    vs=(
                        "%+d:%02d" % (int(was - s["secs"]) // 60, abs(int(was - s["secs"])) % 60)
                        if was and s["secs"]
                        else ""
                    ),
                    faster=bool(was and s["secs"] and was < s["secs"]),
                )
            )
            sp, items, tgt = s["sport"], [], ""
            if sp == "Swim":
                tgt = fd("swim", s["pace_s"])
                items = [
                    "First 100-200 slightly controlled. Don't get dragged out by the start.",
                    f"Settle at ~{tgt}. Draft if you can.",
                    "Sight every 6–8 strokes.",
                ]
            elif sp == "Bike":
                w = s["watts"]
                tgt = f"{w - ftp * .03:.0f}–{w:.0f} W"
                items = [
                    f"First 15–20 min at {ftp * (s['IF'] - .1):.0f}–{ftp * (s['IF'] - .05):.0f} W to settle.",
                    f"Hills: cap at {min(ftp * 1.05, w * 1.15):.0f} W. Surges cost more than they save.",
                    "No power meter: even effort, RPE 5–7/10 depending on length.",
                    "Cadence 85–95.",
                ]
            elif sp == "Run":
                tgt = fd("pace", s["pace_s"])
                first = max(1, round(s["km"] * 0.15 / (KM_MI if imp() else 1)))
                items = [
                    f"First {first} {unit('dist')} at {fd('pace', s['pace_s'] * 1.03)}, slower than feels right.",
                    f"Settle at {tgt}. HR cap first half ~{hz[3][1]:.0f} bpm.",
                    (
                        "Walk steep climbs and aid stations if it keeps effort even."
                        if s["km"] > 30 or s["elev"] > 300
                        else "Run the tangents; relax the shoulders."
                    ),
                    f"Final {max(1, round(s['km'] * .15 / (KM_MI if imp() else 1)))} {unit('dist')}: empty the tank.",
                ]
            else:
                tgt = "Even effort"
                items = [
                    f"Hold Z3–Z4 heart rate ({hz[2][1]:.0f}–{hz[3][2]:.0f} bpm), start conservatively.",
                    "Negative-split if you can: the second half slightly harder.",
                ]
            pacing.append(dict(leg=sp, target=tgt, items=items))
        runs = []
        if "Run" in P["sports"] or any(l["sport"] == "Run" for l in r["legs"]):
            runs = [
                dict(name=n, time=hms(riegel(*run_anchor(P, d), d)), pace=fd("pace", riegel(*run_anchor(P, d), d) / d))
                for n, d in [("5K", 5), ("10K", 10), ("Half marathon", 21.0975), ("Marathon", 42.195), ("50K", 50)]
            ]
        needle = []
        if pr["modelled"]:
            sp = {l["sport"] for l in r["legs"]}
            tries = [
                ("FTP +10 W", "ftp", 10, "Bike"),
                ("CdA −0.02 (aero position)", "cda", -0.02, "Bike"),
                (f"Threshold pace −10 s{unit('pace')}", "run_thr_pace", -10 / (KM_MI if imp() else 1), "Run"),
                (f"CSS −3 s{unit('swim')}", "css", -3, "Swim"),
                (f"Body weight −2 {unit('weight')}", "weight_kg", -2 / (KG_LB if imp() else 1), None),
            ]
            for label, key, delta, need in tries:
                if need and need not in sp:
                    continue
                q = dict(P)
                q[key] += delta
                if key == "run_thr_pace":
                    q["recent_race_km"] = 0
                    q["_no_anchor"] = True
                gain = pr["total"] - predict(q, r, ctl_race)["total"]
                if gain > 0.5:
                    needle.append(dict(label=label, secs=round(gain), time=hms(gain)))
            needle.sort(key=lambda x: -x["secs"])
        checked = set(P.get("checklist", []))
        groups = [g for g in dict.fromkeys([l["sport"] for l in r["legs"]]) if g in CHECK_ITEMS] + ["General"]
        backyard = None
        if "backyard" in r["name"].lower():
            backyard = [
                "Self-supported: set a home base with a table and a cooler of pre-mixed bottles.",
                "Use loops past the house so your aid station comes to you every 20–30 min.",
                "Never swim open water alone — kayak/SUP spotter or a lifeguarded venue, plus a tow float.",
                "Record one multisport file, or start/stop per leg and add the gaps as transitions.",
                "Tell someone your route and ETA. ID + phone with you. Pre-freeze bottles if it's hot.",
            ]
        legs_sports = {l["sport"] for l in r["legs"]}
        warnings = [
            f"{i['name']} ({SEVERITY[i['severity']].lower()}) is active"
            + (
                f" and affects {', '.join(sorted(legs_sports & set(i['sports'])))}"
                if legs_sports & set(i["sports"])
                else ""
            )
            + ". The prediction assumes you're healthy on race day."
            for i in active_on(self._issues(), today)
            if i["kind"] in ("Illness", "Fatigue") or legs_sports & set(i["sports"])
        ]
        weather = None
        if r.get("wx"):
            w, first = r["wx"], r["legs"][0]["sport"]
            pct, too_hot = heat_slowdown(w["temp_max"], w["dew"])
            adv = (
                ["Dangerous heat: slow right down from the start, drink and douse at every aid station."]
                if too_hot
                else (
                    [f"Heat and humidity cost about {pct:.0f}%: it's already in the prediction and paces."]
                    if pct >= 2
                    else []
                )
            )
            adv += ["Thunderstorms forecast: check with the organisers for delays."] if w["code"] >= 95 else []
            weather = dict(
                sky=w["sky"],
                temp=fd("temp", w["temp"]),
                temp_max=fd("temp", w["temp_max"]),
                feels=fd("temp", w["feels"]),
                dew=fd("temp", w["dew"]),
                rain=f"{w['rain']:.0f}%",
                uv=f"{w['uv']:.0f}",
                wind=f"{w['wind'] / 1.609:.0f} mph" if imp() else f"{w['wind']:.0f} km/h",
                start=fmt12(at(race_day, r["start"])),
                wear=what_to_wear(first, "Race pace", w),
                advice=adv,
            )
        goal = None
        if r["goal_s"] and pr["total"]:
            diff = r["goal_s"] - pr["total"]
            goal = dict(time=hms(r["goal_s"]), diff=hms(abs(diff)), ahead=diff >= 0)
        return dict(
            summary=self._race_summary(r, ctl_now, target and target["id"]),
            date=f"{race_day:%A, %B} {race_day.day}, {race_day.year}",
            total=hms(pr["total"]) if pr["total"] else "—",
            lo=hms(pr["lo"]) if pr["lo"] else "",
            hi=hms(pr["hi"]) if pr["hi"] else "",
            modelled=pr["modelled"],
            today_total=hms(now["total"]) if now["total"] else "—",
            ctl_now=round(ctl_now),
            ctl_race=round(ctl_race),
            legs=legs,
            pacing=pacing,
            fueling=race_fueling(P, r, pr),
            runs=runs,
            anchor=(
                "your best recent efforts"
                if _RUN_ANCHORS
                else "your recent race" if P["recent_race_km"] > 0 else "threshold pace ≈ 1 h race pace"
            ),
            needle=needle,
            backyard=backyard,
            goal=goal,
            notes=r["notes"],
            warnings=warnings,
            weather=weather,
            start=fmt12(at(race_day, r["start"])),
            temp_src="forecast" if r.get("wx") else "typed",
            checklist=[
                dict(
                    group=g,
                    items=[
                        dict(key=f"{r['uid']}:{g}:{t}", text=t, done=f"{r['uid']}:{g}:{t}" in checked)
                        for t in CHECK_ITEMS[g]
                    ],
                )
                for g in groups
            ],
        )

    @_locked
    def toggle_check(self, key, on):
        s = set(P.get("checklist", []))
        s.add(key) if on else s.discard(key)
        P["checklist"] = sorted(s)
        self._save()

    # ---- nutrition
    @_locked
    def nutrition(self, day=None):
        try:
            day = dt.date.fromisoformat(day)
        except (TypeError, ValueError):
            day = dt.date.today()
        logged = [w for w in self._workouts() if w["date"] == day.isoformat()]
        _, weeks = self._plan()
        planned = [s for w in weeks for s in w["sessions"] if s[0] == day]
        if logged:
            sess = [(w["sport"], w["dur_s"], w["kcal"] or 0, rpe_if(w["rpe"]) if w["rpe"] else 0.72) for w in logged]
            src = "Logged workouts"
        else:
            sess = [
                (s[1], s[2], estimate_kcal(P, s[1], s[2], tss=s[3]), math.sqrt(s[3] / (s[2] / 36)) if s[2] else 0.7)
                for s in planned
                if s[1] not in ("Race", "Rest")
            ]
            src = "Planned sessions" if sess else "Rest day"
        n = daily_nutrition(P, [(s, d, k) for s, d, k, _ in sess], P["goal"])
        kg = P["weight_kg"]
        macros = [
            dict(name="Carbs", g=round(n["carbs"]), gkg=round(n["carbs"] / kg, 1), kcal=round(4 * n["carbs"])),
            dict(name="Protein", g=round(n["protein"]), gkg=round(n["protein"] / kg, 1), kcal=round(4 * n["protein"])),
            dict(name="Fat", g=round(n["fat"]), gkg=round(n["fat"] / kg, 1), kcal=round(9 * n["fat"])),
        ]
        race = next((s for s in planned if s[1] == "Race"), None)
        day_wx = (
            wx_during(self._wx, dt.datetime.combine(day, dt.time(11)), dt.datetime.combine(day, dt.time(18)))
            if self._wx
            else None
        )
        hot = bool(day_wx and day_wx["temp_max"] >= 24)
        heat = None
        if day_wx:
            pct = heat_slowdown(day_wx["temp_max"], day_wx["dew"])[0] if day_wx["dew"] is not None else 0
            extra = 0.75 if pct >= 4 else 0.5 if hot else 0
            heat = dict(
                temp=fd("temp", day_wx["temp_max"]),
                sky=day_wx["sky"].lower(),
                extra=fd("vol", extra) if extra else "",
                note=(
                    f"Hot day: drink about {fd('vol', extra)} more than usual, salt your food, and take electrolytes "
                    "in any session over an hour."
                    if extra
                    else "Normal fluid needs today."
                ),
            )
        key_sess = max(sess, key=lambda s: s[1], default=None)  # the day's longest session, if any
        caffeine = dict(
            habitual_mg=round(P.get("caffeine_mg") or 0), sensitivity=P.get("caffeine_sensitivity") or "normal"
        )
        if key_sess and key_sess[1] >= 2700 and key_sess[0] != "Race":  # worth a dosing strategy from ~45 min up
            dose = caffeine_dose(P, key_sess[1])
            caffeine["session"] = dict(sport=key_sess[0], dur=hms(key_sess[1]), **dose)
        return dict(
            date=day.isoformat(),
            nice=f"{day:%A, %B} {day.day}",
            src=src,
            goal=P["goal"],
            activity=P["activity"],
            hours=round(n["hours"], 1),
            kcal=round(n["kcal"]),
            bmr=round(n["bmr"]),
            life=round(n["life"]),
            train=round(n["train_kcal"]),
            tdee=round(n["tdee"]),
            macros=macros,
            protein_meal=f"{0.3 * kg:.0f}–{0.4 * kg:.0f} g",
            fluids=fd("vol", 0.035 * kg),
            sessions=[dict(sport=s, dur=hms(d), lines=fuel_session(P, s, d, IF, hot)) for s, d, _, IF in sess],
            heat=heat,
            race=dict(id=race[5], name=race[4].split(" (")[0]) if race else None,
            sweat_rate=fd("vol", P["sweat_rate"]),
            caffeine=caffeine,
            principles=[
                ("Fuel the work", "Carbs rise and fall with training load. Hard or long days are not the day to diet."),
                (
                    "Lose weight slowly",
                    "Deficits on easy days only, protein 2.0–2.4 g/kg, max ~0.5–0.7% body weight/week.",
                ),
                ("Train the gut", "Practise race carbs (60–90 g/h, 2:1 glucose:fructose) in long sessions."),
                ("Watch the gaps", "Iron, vitamin D and calcium are common gaps. Get bloodwork if fatigue lingers."),
                (
                    "Don't under-fuel",
                    "Low energy availability wrecks hormones, bones and adaptation. Stalled performance, "
                    "frequent illness or lost periods mean eat more and see a sports dietitian.",
                ),
                ("Sleep on protein", "After big days, 30–40 g casein / Greek yogurt / cottage cheese before bed."),
            ],
        )

    @_locked
    def sweat_test(self, f):
        try:
            pre, post = from_ui("weight", f["pre"]), from_ui("weight", f["post"])
            drank, h = from_ui("vol", f.get("drank") or 0), float(f["mins"]) / 60
            rate = (pre - post + drank) / h
            if not 0.1 < rate < 4:
                raise ValueError(f"{rate:.2f} L/h is outside a plausible range")
        except (ValueError, KeyError, ZeroDivisionError) as e:
            return dict(ok=False, error=str(e) or "Check the inputs")
        P["sweat_rate"] = round(rate, 2)
        self._save()
        lost = (pre - post) / pre * 100
        return dict(ok=True, rate=fd("vol", rate), lost=round(lost, 1), warn=lost > 2)

    # ---- wellness
    @_locked
    def wellness(self):
        rows = self._wellness()
        series = self._series()
        score, notes = readiness(rows, series[-1][3], active_on(self._issues(), dt.date.today()))
        o = lambda v, k="float": to_ui(k, v) if v is not None else ""
        asc = list(reversed(rows[:60]))
        today = dt.date.today()
        wts = [(dt.date.fromisoformat(r["date"]), r["weight_kg"]) for r in rows if r["weight_kg"]]
        a = [w for d, w in wts if (today - d).days < 7]
        b = [w for d, w in wts if 7 <= (today - d).days < 14]
        trend = None
        if a and b:
            ch = sum(a) / len(a) - sum(b) / len(b)
            pct = ch / (sum(b) / len(b)) * 100
            trend = dict(
                text=f"{'+' if ch >= 0 else '−'}{to_ui('weight', abs(ch))} {unit('weight')}/wk",
                pct=round(pct, 1),
                warn=pct < -1,
            )
        val = lambda v, k=None: (float(to_ui(k, v)) if k else round(v, 1)) if v is not None else None
        return dict(
            rows=[
                dict(
                    date=r["date"],
                    nice=_nice_date(dt.date.fromisoformat(r["date"])),
                    weight=o(r["weight_kg"], "weight"),
                    sleep=o(r["sleep_h"]),
                    rhr=o(r["rhr"]),
                    hrv=o(r["hrv"]),
                    soreness=o(r["soreness"]),
                    stress=o(r["stress"]),
                    fatigue=o(r["fatigue"]),
                    mood=o(r["mood"]),
                    notes=r["notes"] or "",
                )
                for r in rows
            ],
            score=score,
            notes=notes,
            trend=trend,
            weight_unit=unit("weight"),
            charts=dict(
                labels=[r["date"] for r in asc],
                weight=[val(r["weight_kg"], "weight") for r in asc],
                rhr=[val(r["rhr"]) for r in asc],
                hrv=[val(r["hrv"]) for r in asc],
                sleep=[val(r["sleep_h"]) for r in asc],
                fatigue=[val(r["fatigue"]) for r in asc],
            ),
            signals=fatigue_signals(rows, series, today),
            today=today.isoformat(),
            weight=to_ui("weight", P["weight_kg"]),
        )

    @_locked
    def save_wellness(self, f):
        kinds = dict(
            date="date",
            weight_kg="weight",
            sleep_h="float",
            rhr="float",
            hrv="float",
            soreness="int",
            stress="int",
            fatigue="int",
            mood="int",
            notes="str",
        )
        try:
            v = {k: (from_ui(kind, f.get(k)) if str(f.get(k) or "").strip() else None) for k, kind in kinds.items()}
            if not v["date"]:
                raise ValueError("Date required")
            for k in ("soreness", "stress", "fatigue", "mood"):
                if v[k] is not None and not 1 <= v[k] <= 5:
                    raise ValueError(f"{k.title()} must be 1–5")
        except ValueError as e:
            return dict(ok=False, error=str(e))
        latest = max([r["date"] for r in self._wellness()] + [""])
        self._db.execute(
            f"INSERT OR REPLACE INTO wellness({','.join(kinds)}) VALUES({','.join('?' * len(kinds))})",
            tuple(v[k] for k in kinds),
        )
        self._db.commit()
        if v["weight_kg"] and v["date"] >= latest:
            P["weight_kg"] = round(v["weight_kg"], 2)
            self._save()
        return dict(ok=True)

    @_locked
    def delete_wellness(self, date):
        return self._take("wellness", "date", [date])

    # ---- health issues
    def _issue_view(self, i, today):
        start = dt.date.fromisoformat(i["start"])
        end = dt.date.fromisoformat(i["end"]) if i["end"] else None
        area = BODY.get(i["area"], BODY["Other"]) if i["kind"] == "Injury" else None
        active = start <= today and (not end or today <= end)
        ramp_left = max(0, (i["ramp_days"] or 0) - (today - end).days) if end else 0
        return dict(
            i,
            active=active,
            days=((end or today) - start).days + 1,
            since=f"{start:%b} {start.day}",
            until=f"{end:%b} {end.day}" if end else "",
            sev_label=SEVERITY[i["severity"]],
            sev_help=SEVERITY_HELP[i["severity"]],
            rehab=area[1] if area else "",
            red_flags=area[2] if area else "",
            guidance=KIND_GUIDANCE.get(i["kind"], KIND_GUIDANCE["Other"]),
            ramp_left=ramp_left,
        )

    @_locked
    def health(self):
        today = dt.date.today()
        issues = [self._issue_view(i, today) for i in self._issues()]
        series = self._series()
        return dict(
            active=[i for i in issues if i["active"]],
            past=[i for i in issues if not i["active"]],
            signals=fatigue_signals(self._wellness(), series, today),
            kinds=ISSUE_KINDS,
            areas=list(BODY),
            severity=SEVERITY,
            severity_help=SEVERITY_HELP,
            area_sports={k: v[0] for k, v in BODY.items()},
            sports=self._sports(),
            today=today.isoformat(),
        )

    @_locked
    def save_issue(self, f):
        try:
            kind = f.get("kind")
            if kind not in ISSUE_KINDS:
                raise ValueError("Pick a type")
            sev = int(f.get("severity") or 0)
            if not 1 <= sev <= 5:
                raise ValueError("Severity must be 1-5")
            start = dt.date.fromisoformat(f.get("start") or "").isoformat()
            end = dt.date.fromisoformat(f["end"]).isoformat() if f.get("end") else None
            if end and end < start:
                raise ValueError("Resolved date is before the start date")
            area = f.get("area") if kind == "Injury" else ""
            name = (f.get("name") or "").strip() or " ".join(
                x for x in (f.get("side"), area.lower() if area else "", kind.lower()) if x
            ).capitalize()
            sports = [x for x in ALL_SPORTS if x in (f.get("sports") or [])] if kind in ("Injury", "Other") else []
            rec = (
                kind,
                name,
                area,
                f.get("side") or "",
                sev,
                json.dumps(sports),
                start,
                end,
                (f.get("notes") or "").strip(),
            )
        except (ValueError, TypeError) as e:
            return dict(ok=False, error=str(e) or "Check the form")
        if f.get("id"):
            self._db.execute(
                'UPDATE issues SET kind=?,name=?,area=?,side=?,severity=?,sports=?,start=?,"end"=?,notes=? WHERE id=?',
                rec + (int(f["id"]),),
            )
        else:
            self._db.execute(
                'INSERT INTO issues(kind,name,area,side,severity,sports,start,"end",notes) VALUES(?,?,?,?,?,?,?,?,?)',
                rec,
            )
        self._db.commit()
        return dict(ok=True)

    @_locked
    def suggest_ramp(self, iid):
        i = next((x for x in self._issues() if x["id"] == int(iid)), None)
        if not i:
            return dict(ok=False, error="Issue not found")
        return dict(ok=True, days=suggest_ramp_days(i, dt.date.today().isoformat()))

    @_locked
    def resolve_issue(self, iid, ramp_days=None):
        i = next((x for x in self._issues() if x["id"] == int(iid)), None)
        if not i:
            return dict(ok=False, error="Issue not found")
        end = dt.date.today().isoformat()
        ramp = int(ramp_days) if ramp_days not in (None, "") else suggest_ramp_days(i, end)
        ramp = max(0, min(42, ramp))
        self._db.execute('UPDATE issues SET "end"=?,ramp_days=? WHERE id=?', (end, ramp, int(iid)))
        self._db.commit()
        return dict(ok=True, ramp_days=ramp)

    @_locked
    def delete_issue(self, iid):
        return self._take("issues", "id", [int(iid)])

    # ---- gear: shoes, bikes, chains, tyres, wetsuits - mileage/time accrue from the workout log, not hand-entry
    def _gear_view(self, g, totals):
        dist_km, dur_s = totals.get(g["id"], (0, 0))
        pct = round(dist_km / g["retire_km"] * 100) if g["retire_km"] else None
        return dict(
            g,
            dist=fd("dist", dist_km),
            dur=hms(dur_s),
            retire=fd("dist", g["retire_km"]) if g["retire_km"] else "",
            retire_ui=to_ui("dist", g["retire_km"]) if g["retire_km"] else "",
            pct=pct,
            warn="" if pct is None else "bad" if pct >= 100 else "warn" if pct >= GEAR_WARN_PCT else "",
        )

    @_locked
    def gear(self):
        totals = self._gear_totals()
        return dict(
            items=[self._gear_view(g, totals) for g in self._gear()],  # already active-first, then by name
            sports=self._sports(),
            dist_unit=unit("dist"),
        )

    @_locked
    def save_gear(self, f):
        try:
            name = (f.get("name") or "").strip()
            if not name:
                raise ValueError("Enter a name")
            kind = (f.get("kind") or "").strip() or "Other"
            sports = [x for x in ALL_SPORTS if x in (f.get("sports") or [])]
            if not sports:
                raise ValueError("Pick at least one sport")
            purchased = dt.date.fromisoformat(f["purchased"]).isoformat() if f.get("purchased") else ""
            retire_km = from_ui("dist", f["retire"]) if str(f.get("retire") or "").strip() else None
            if retire_km is not None and not retire_km > 0:
                raise ValueError("Retire-at distance must be greater than 0")
            is_default = bool(f.get("is_default"))
            notes = (f.get("notes") or "").strip()
        except (ValueError, TypeError) as e:
            return dict(ok=False, error=str(e) or "Check the form")
        gid = int(f["id"]) if f.get("id") else None
        rec = (name, kind, json.dumps(sports), purchased, retire_km, int(is_default), notes)
        if gid:
            self._db.execute(
                "UPDATE gear SET name=?,kind=?,sports=?,purchased=?,retire_km=?,is_default=?,notes=? WHERE id=?",
                rec + (gid,),
            )
        else:
            self._db.execute(
                "INSERT INTO gear(name,kind,sports,purchased,retire_km,active,is_default,notes) "
                "VALUES(?,?,?,?,?,1,?,?)",
                rec,
            )
            gid = self._db.execute("SELECT last_insert_rowid()").fetchone()[0]
        if is_default:  # only one default per sport: unclaim it from any other item that shares one
            for g in self._gear():
                if g["id"] != gid and g["is_default"] and set(g["sports"]) & set(sports):
                    self._db.execute("UPDATE gear SET is_default=0 WHERE id=?", (g["id"],))
        self._db.commit()
        return dict(ok=True)

    @_locked
    def set_gear_active(self, gid, active):
        self._db.execute("UPDATE gear SET active=? WHERE id=?", (1 if active else 0, int(gid)))
        self._db.commit()
        return dict(ok=True)

    @_locked
    def delete_gear(self, gid):
        return self._take("gear", "id", [int(gid)])

    # ---- first-run setup
    @_locked
    def setup_info(self):
        groups = {}
        for n, (g, _) in PRESETS.items():
            if g != "Custom":
                groups.setdefault(g, []).append(n)
        return dict(
            levels=[dict(key=k, label=v["label"], sub=v["sub"], hours=v["hours"]) for k, v in LEVELS.items()],
            all_sports=ALL_SPORTS,
            presets=groups,
            done=P.get("setup_done", False),
            values=dict(
                name=P["name"],
                units=P["units"],
                sex=P["sex"],
                theme=P.get("theme", "system"),
                # fresh installs start blank so nobody keeps the placeholder body stats by accident
                age=P["age"] if P.get("setup_done") else "",
                weight=to_ui("weight", P["weight_kg"]) if P.get("setup_done") else "",
                height=to_ui("height", P["height_cm"]) if P.get("setup_done") else "",
                sports=P["sports"],
                days=P["days_per_week"],
                long_day=P["long_day"],
            ),
            today=dt.date.today().isoformat(),
        )

    @_locked
    def complete_setup(self, f):
        """Apply the wizard in one go. Blank fitness fields are estimated from experience level, age and weight."""
        try:
            P["units"] = f.get("units") if f.get("units") in ("imperial", "metric") else P["units"]
            age = int(float(f.get("age") or 0))
            kg, cm = from_ui("weight", f.get("weight") or 0), from_ui("height", f.get("height") or 0)
            if not 10 <= age <= 100:
                raise ValueError("Enter an age between 10 and 100", 0)
            if not 30 <= kg <= 250 or not 120 <= cm <= 230:
                raise ValueError("Check your weight and height", 0)
            sports = [x for x in ALL_SPORTS if x in (f.get("sports") or [])]
            if not sports:
                raise ValueError("Pick at least one sport", 1)
            L = LEVELS.get(f.get("level"))
            if not L:
                raise ValueError("Pick your experience level", 1)
            hours = float(f.get("hours") or L["hours"][0])
            num_or = lambda k, default: float(f[k]) if str(f.get(k) or "").strip() else default
            max_hr = num_or("max_hr", round(208 - 0.7 * age))  # Tanaka
            est = {
                "ftp": not str(f.get("ftp") or "").strip(),
                "css": not str(f.get("css") or "").strip(),
                "max_hr": not str(f.get("max_hr") or "").strip(),
            }
            upd = dict(
                name=(f.get("name") or "").strip(),
                sex=f.get("sex") if f.get("sex") in ("M", "F") else "M",
                age=age,
                weight_kg=kg,
                height_cm=cm,
                sports=sports,
                theme=f.get("theme") or "system",
                ftp=num_or("ftp", round(L["wkg"] * kg / 5) * 5),
                max_hr=max_hr,
                lthr=round(max_hr * 0.89),
                rest_hr=num_or("rest_hr", 60),
                weekly_hours=hours,
                peak_hours=max(hours + 2, L["hours"][1]),
                days_per_week=int(f.get("days") or 6),
                long_day=int(f.get("long_day") or 6),
                css=from_ui("swim", f["css"]) if not est["css"] else L["css"],
                plan_start=dt.date.today().isoformat(),
                plan_race="",
                setup_done=True,
            )
            mode = f.get("run_mode")
            if mode == "race":
                km, t = float(f.get("run_race_km") or 0), parse_clock(f.get("run_race_time") or 0)
                if km <= 0 or t <= 0:
                    raise ValueError("Enter your race distance and finish time, or pick another option", 2)
                upd.update(run_thr_pace=threshold_from_race(km, t), recent_race_km=km, recent_race_s=t)
            elif mode == "pace":
                upd.update(run_thr_pace=from_ui("pace", f.get("run_pace") or ""), recent_race_km=0.0, recent_race_s=0.0)
            else:
                upd.update(run_thr_pace=L["thr"], recent_race_km=0.0, recent_race_s=0.0)
            est["run"] = mode not in ("race", "pace")
            if not 150 < upd["run_thr_pace"] < 900 or not 40 < upd["css"] < 400 or not 50 < upd["ftp"] < 600:
                raise ValueError("One of your fitness numbers looks off. Check the format (m:ss for paces)", 2)
        except (ValueError, TypeError) as e:
            msg, step = (e.args + (None, None))[:2] if e.args else ("Check the form", None)
            return dict(ok=False, error=str(msg), step=step if isinstance(step, int) else 2)
        P.update(upd)
        self._save()
        race = None
        if f.get("race_preset") in PRESETS and f.get("race_date"):
            legs = [dict(sport=sp, dist=leg_dist_ui(sp, km), elev="0") for sp, km in PRESETS[f["race_preset"]][1]]
            r = self.save_race(
                dict(
                    name=(f.get("race_name") or "").strip() or f["race_preset"],
                    date=f["race_date"],
                    preset=f["race_preset"],
                    priority="A",
                    legs=legs,
                    temp=to_ui("temp", 18),
                )
            )
            if not r["ok"]:
                return dict(ok=False, error=r["error"], step=3)
            race = f.get("race_name") or f["race_preset"]
        hz = hr_zones(P)
        return dict(
            ok=True,
            race=race,
            summary=[
                dict(
                    label="Run threshold pace",
                    value=fd("pace", P["run_thr_pace"]),
                    est=est["run"],
                    show="Run" in sports,
                ),
                dict(label="Bike FTP", value=f"{P['ftp']:.0f} W", est=est["ftp"], show="Bike" in sports),
                dict(label="Swim CSS", value=fd("swim", P["css"]), est=est["css"], show="Swim" in sports),
                dict(label="Max heart rate", value=f"{P['max_hr']:.0f} bpm", est=est["max_hr"], show=True),
                dict(
                    label="Easy (Z2) heart rate",
                    value=f"{hz[1][1]:.0f}–{hz[1][2]:.0f} bpm",
                    est=est["max_hr"],
                    show=True,
                ),
                dict(
                    label="Weekly hours", value=f"{P['weekly_hours']:g} → {P['peak_hours']:g} h", est=False, show=True
                ),
            ],
        )

    # ---- sync: phone side
    @_locked
    def sync_request(self):
        """What the phone sends to the desktop hub. `mark` is confirmed with sync_response once the hub accepted it."""
        return dict(
            host=P["sync_host"],
            code=P["sync_code"],
            mark=current_rev(self._db),
            body=dict(
                since=P["sync_remote_rev"],
                device=this_device(P),
                changes=collect_changes(self._db, P["sync_pushed_rev"]),
            ),
        )

    @_locked
    def sync_response(self, resp, mark):
        # a device that is itself a hub re-stamps what it receives so its own clients get it too; the echo back
        # to the upstream hub is harmless, last-writer-wins drops it on arrival
        n = apply_changes(self._db, resp["changes"], hub=bool(self._hub))
        load_profile(self._db)
        P.update(
            sync_remote_rev=resp["changes"]["rev"],
            sync_pushed_rev=int(mark),
            sync_last=dt.datetime.now().isoformat(timespec="seconds"),
        )
        save_profile(self._db, touch=False)
        return dict(ok=True, received=n, sent=resp.get("received", 0), hub=resp.get("name", ""))

    @_locked
    def sync_pair(self, host, code):
        P.update(
            sync_host=(host or "").strip(), sync_code=(code or "").strip().upper(), sync_remote_rev=0, sync_pushed_rev=0
        )
        save_profile(self._db, touch=False)
        return dict(ok=True)

    @_locked
    def sync_set_host(self, host):
        """The PC moved to a new address (found by discovery): keep sync progress, just update where it lives."""
        P["sync_host"] = (host or "").strip()
        save_profile(self._db, touch=False)
        return dict(ok=True)

    @_locked
    def sync_unpair(self):
        P.update(sync_host="", sync_code="", sync_remote_rev=0, sync_pushed_rev=0, sync_last="")
        save_profile(self._db, touch=False)
        return dict(ok=True)

    def sync_now(self):
        """One sync against the hub this device is paired with. The phone overrides this with its own driver in
        bridge.js (native HTTP); this is the computer's, so a laptop pairs exactly the way a phone does.
        Deliberately not @_locked: it blocks on the network, and the pieces it calls take the lock themselves."""
        req = self.sync_request()
        if not req["code"]:
            return dict(ok=False, error="This device isn't paired with another one yet.")
        host = req["host"] and (req["host"] if ":" in req["host"] else f"{req['host']}:{SYNC_PORTS[0]}")
        status, data = post_sync(host, req["code"], req["body"]) if host else (None, {})
        moved = None
        if status is None:
            moved = host = discover_hub(host, req["code"])
            if not host:
                return dict(
                    ok=False,
                    error="Couldn't find that device on this network. Check both are on the same "
                    "Wi-Fi, the other one is open with Device sync on, and its firewall allows it.",
                )
            self.sync_set_host(host)
            status, data = post_sync(host, req["code"], req["body"])
            if status is None:
                return dict(ok=False, error=f"Found it at {host} but the sync didn't finish. Try again.")
        if status != 200:
            return dict(ok=False, error=data.get("error") or f"The other device replied {status}")
        return dict(**self.sync_response(data, req["mark"]), moved=moved)

    def find_hubs(self):
        """Devices advertising a hub on this network right now. The pairing screen lists these by name so
        nobody has to read an address off one screen and type it into another.
        Not @_locked: it waits on the network for a couple of seconds and holds nothing the lock protects."""
        mine = {f"{ip}:{self._hub.server_address[1]}" for ip in lan_addresses()} if self._hub else set()
        return dict(hubs=[dict(host=h, name=n) for h, n in browse_hubs() if h not in mine])

    def _seen_device(self, dev):
        """The hub's roster of what has synced with it. Local to the hub - it is about machines, not training."""
        if not (dev or {}).get("id"):
            return
        seen = json.loads(kv_get(self._db, "devices", "{}"))
        seen[str(dev["id"])[:40]] = dict(
            name=str(dev.get("name") or "Device")[:40],
            kind=dev.get("kind") or "device",
            last=dt.datetime.now().isoformat(timespec="seconds"),
        )
        self._db.execute("INSERT OR REPLACE INTO kv VALUES('devices', ?)", (json.dumps(seen),))

    @_locked
    def devices(self):
        """Everything that has synced with this hub, newest first, plus what this device calls itself."""
        seen = json.loads(kv_get(self._db, "devices", "{}"))
        me = this_device(P)
        save_profile(self._db, touch=False)
        return dict(
            me=me,
            paired=bool(P["sync_host"]),
            host=P["sync_host"],
            last=P["sync_last"],
            list=sorted((dict(id=k, **v) for k, v in seen.items()), key=lambda d: d["last"], reverse=True),
        )

    @_locked
    def rename_device(self, name):
        P["device_name"] = (name or "").strip()[:40] or device_label()
        save_profile(self._db, touch=False)
        return dict(ok=True, name=P["device_name"])

    @_locked
    def forget_device(self, device_id):
        seen = json.loads(kv_get(self._db, "devices", "{}"))
        seen.pop(device_id, None)
        self._db.execute("INSERT OR REPLACE INTO kv VALUES('devices', ?)", (json.dumps(seen),))
        self._db.commit()
        return dict(ok=True)

    # ---- sync: desktop hub side
    def hub_exchange(self, body):
        """Handle one phone sync: merge its changes, return ours since its last sync."""
        with self._lock:
            n = apply_changes(self._db, body.get("changes") or {}, hub=True)
            if n:
                load_profile(self._db)
            P["hub_last"] = dt.datetime.now().isoformat(timespec="seconds")
            self._seen_device(body.get("device"))
            save_profile(self._db, touch=False)
            out = dict(changes=collect_changes(self._db, int(body.get("since") or 0)), received=n, name=P["name"])
        if n and self._window:
            self._window.evaluate_js(f"window.onSynced && onSynced({n})")
        return out

    @_locked
    def hub_status(self):
        port = self._hub.server_address[1] if self._hub else None
        d = self.devices()
        return dict(
            on=bool(self._hub),
            code=P["hub_code"],
            port=port,
            addresses=[f"{ip}:{port}" for ip in lan_addresses()] if port else [],
            last=P["hub_last"],
            me=d["me"],
            devices=d["list"],
            paired=d["paired"],
            host=d["host"],
            synced=d["last"],
            can_relay=not IS_PHONE,
            serve_assets=bool(P.get("serve_assets")),
            assets=[n for n in ASSET_FILES if os.path.exists(resource(n))],
        )

    @_locked
    def serve_assets_set(self, on):
        """Let paired devices fetch this device's ui.html and endurance.py, so the phone can run today's code."""
        P["serve_assets"] = bool(on)
        save_profile(self._db, touch=False)
        return self.hub_status()

    def hub_set(self, on):
        with self._lock:
            if on and not self._hub:
                if not P["hub_code"]:
                    P["hub_code"] = new_pairing_code()
                self._hub = start_hub(self)
            elif not on and self._hub:
                stop_advertising(getattr(self._hub, "mdns", None))
                self._hub.shutdown()
                self._hub.server_close()
                self._hub = None
            P["hub_on"] = bool(self._hub)
            save_profile(self._db, touch=False)
        return self.hub_status()

    @_locked
    def hub_new_code(self):
        P["hub_code"] = new_pairing_code()
        save_profile(self._db, touch=False)
        return self.hub_status()

    # ---- life: habits, sleep, reminders, motivation, notifications
    def _habits(self):
        return [dict(r) for r in self._db.execute("SELECT * FROM habits WHERE NOT archived ORDER BY sort, id")]

    def _done_dates(self, uid):
        return {r["date"] for r in self._db.execute("SELECT date FROM habit_log WHERE habit=? AND done", (uid,))}

    def _quotes(self):
        return [dict(r) for r in self._db.execute("SELECT * FROM quotes ORDER BY uid")]

    def _quote_for(self, day, offset=0):
        qs = self._quotes()
        return qs[(day.toordinal() + offset) % len(qs)] if qs else None

    def _open_items(self, day, weeks=None):
        """What's still to do on `day`: planned sessions not logged, scheduled habits not ticked."""
        weeks = weeks if weeks is not None else self._plan()[1]
        planned = [x for w in weeks for x in w["sessions"] if x[0] == day and x[1] not in ("Race", "Rest")]
        items = [TEAM_TAG if is_team(x) else f"{x[1]} session" for x in not_done(planned, self._workouts(), day)]
        for h in self._habits():
            if day.weekday() in json.loads(h["days"]) and day.isoformat() not in self._done_dates(h["uid"]):
                items.append(h["name"])
        return items

    @_locked
    def life(self):
        today = dt.date.today()
        habits = []
        for h in self._habits():
            sched, done = json.loads(h["days"]), self._done_dates(h["uid"])
            first = min(done, default=today.isoformat())  # days before tracking started aren't "missed"
            week = [
                dict(
                    day=f"{d:%a}"[0],
                    date=d.isoformat(),
                    state=(
                        "done"
                        if d.isoformat() in done
                        else (
                            "off"
                            if d.weekday() not in sched
                            else "future" if d >= today or d.isoformat() < first else "missed"
                        )
                    ),
                )
                for d in (today - dt.timedelta(days=6 - k) for k in range(7))
            ]
            habits.append(
                dict(
                    uid=h["uid"],
                    name=h["name"],
                    days=sched,
                    today=today.weekday() in sched,
                    done=today.isoformat() in done,
                    streak=streak(done, sched, today),
                    week=week,
                )
            )
        tonight = bedtime_before(P, today + ONE)
        nights = [r["sleep_h"] for r in self._wellness()[:7] if r["sleep_h"]]
        return dict(
            habits=habits,
            today=today.isoformat(),
            reminders=[
                dict(
                    uid=r["uid"],
                    title=r["title"],
                    time=r["time"],
                    days=json.loads(r["days"]),
                    active=bool(r["active"]),
                    nice=fmt12(at(today, r["time"])),
                )
                for r in self._db.execute("SELECT * FROM reminders ORDER BY time")
            ],
            quotes=self._quotes(),
            quote=self._quote_for(today),
            sleep=dict(
                goal=sleep_goal(P),
                bedtime=fmt12(tonight),
                wake=fmt12(wake_on(P, today + ONE)),
                tomorrow=(today + ONE).isoformat(),
                wake_clock=f"{wake_on(P, today + ONE):%H:%M}",
                wake_once=(P.get("wake_once") or {}).get((today + ONE).isoformat()),
                winddown=fmt12(tonight - dt.timedelta(minutes=int(P["winddown"] or 0))),
                avg=round(sum(nights) / len(nights), 1) if nights else None,
                nights=len(nights),
            ),
            settings=self._fields(LIFE_KEYS),
            open=self._open_items(today),
        )

    @_locked
    def set_wake(self, date, hhmm):
        """Wake-up for one date only; empty hhmm goes back to the usual time. Past dates are pruned."""
        today = dt.date.today().isoformat()
        once = {d: t for d, t in (P.get("wake_once") or {}).items() if d >= today and d != date}
        if hhmm:
            try:
                h, m = clock(hhmm)
            except (ValueError, TypeError):
                return dict(ok=False, error="Pick a time")
            once[date] = f"{h:02d}:{m:02d}"
        P["wake_once"] = once
        self._save()
        return dict(ok=True)

    # ---- sessions the athlete schedules
    @_locked
    def schedule_form(self, uid=None):
        sc = next((x for x in self._scheduled() if x["uid"] == uid), None)
        tomorrow = (dt.date.today() + ONE).isoformat()
        v = sc or dict(
            date=tomorrow,
            time="07:00",
            sport=self._sports()[0] if "Run" not in self._sports() else "Run",
            kind="Easy",
            dur_s=0,
            dist_km=0,
            notes="",
        )
        h, r = divmod(int(v["dur_s"] or 0), 3600)
        return dict(
            uid=uid,
            date=v["date"],
            time=v["time"],
            sport=v["sport"],
            kind=v["kind"],
            notes=v["notes"],
            dist=leg_dist_ui(v["sport"], v["dist_km"]) if v["dist_km"] else "",
            h=h or "",
            m=r // 60 or "",
            sports=[x for x in self._sports() if x not in ("Strength", "Mobility")] or ["Run"],
            kinds=list(SCHED_KINDS),
            dist_unit=unit("dist"),
            swim_unit="yd" if imp() else "m",
            place=P["home_place"],
        )

    def _usual_duration(self, sport, kind, day):
        """How long the plan would have had you do `sport` that week: that day's session, else the week's typical one."""
        _, weeks = self._plan()
        d = dt.date.fromisoformat(day)
        wk = next((w for w in weeks if w["start"] <= d < w["start"] + 7 * ONE), None)
        same = [x for x in (wk["sessions"] if wk else []) if x[1] == sport and not isinstance(x[5], str) and x[2]]
        if not same:
            return 2700.0
        on_day = [x[2] for x in same if x[0] == d]
        secs = on_day[0] if on_day else max(x[2] for x in same) if kind == "Long" else sum(x[2] for x in same) / len(same)
        return float(round(secs / 300) * 300) or 2700.0

    @_locked
    def save_scheduled(self, f):
        try:
            day = dt.date.fromisoformat(f.get("date") or "").isoformat()
            hh, mm = clock(f.get("time") or "")
        except (ValueError, TypeError):
            return dict(ok=False, error="Pick a day and a start time")
        sport = f.get("sport") if f.get("sport") in ALL_SPORTS else "Run"
        kind = f.get("kind") if f.get("kind") in SCHED_KINDS else "Easy"
        try:
            dist = leg_dist_from(sport, f.get("dist") or 0)
            dur = float(f.get("h") or 0) * 3600 + float(f.get("m") or 0) * 60
        except (ValueError, TypeError):
            return dict(ok=False, error="Check the distance and duration")
        sc = dict(
            uid=f.get("uid"),
            date=day,
            time=f"{hh:02d}:{mm:02d}",
            sport=sport,
            kind=kind,
            dur_s=dur,
            dist_km=dist,
            notes=(f.get("notes") or "").strip(),
        )
        if not sched_duration(P, sc) and f.get("auto"):
            sc["dur_s"] = dur = self._usual_duration(sport, kind, day)
        if not sched_duration(P, sc):
            return dict(
                ok=False,
                error="Enter a duration" + (" or a distance" if sport in PACED or sport in ("Bike", "Swim") else ""),
            )
        rec = (day, sc["time"], sport, kind, dur or None, dist or None, sc["notes"])
        if f.get("uid"):
            self._db.execute(
                "UPDATE scheduled SET date=?, time=?, sport=?, kind=?, dur_s=?, dist_km=?, notes=? WHERE uid=?",
                rec + (f["uid"],),
            )
        else:
            self._db.execute(
                "INSERT INTO scheduled(date, time, sport, kind, dur_s, dist_km, notes) VALUES(?,?,?,?,?,?,?)", rec
            )
        self._db.commit()
        return dict(ok=True)

    @_locked
    def delete_scheduled(self, uid):
        return self._take("scheduled", "uid", [uid])

    @_locked
    def session_brief(self, uid, wx=None):
        wx = wx or self._wx
        sc = next((x for x in self._scheduled() if x["uid"] == uid), None)
        if not sc:
            return None
        series = self._series()
        today = dt.date.today()
        day = dt.date.fromisoformat(sc["date"])
        ready = (
            readiness(self._wellness(), series[-1][3], active_on(self._issues(), today))[0]
            if day <= today + ONE
            else None
        )
        out = session_brief(P, sc, wx, series[-1][3], ready, active_on(self._issues(), day))
        out["place"] = P["home_place"]
        return out

    def _wx_line(self, s):
        """'4:00 PM: 72°F, cloudy · better at 7:00 AM' for an outdoor session, or ''."""
        if not self._wx or s[1] not in OUTDOOR or s[1] == "Race":
            return ""
        t = self._scheduled_time(s)
        start = at(s[0], t)
        w = wx_during(self._wx, start, start + dt.timedelta(seconds=s[2] or 3600))
        if not w:
            return ""
        return f"{fmt12(start)}: {wx_short(w)}" + (
            " · thunderstorms" if w["code"] >= 95 and "thunder" not in w["sky"].lower() else ""
        )

    def _scheduled_time(self, s):
        if isinstance(s[5], str):
            sc = next((x for x in self._scheduled() if x["uid"] == s[5][2:]), None)
            if sc:
                return sc["time"]
        return session_time(P, s)

    @_locked
    def plan_brief(self, date, k):
        """Briefing for any planned session (the k-th on that day), at your usual training or practice time."""
        day = dt.date.fromisoformat(date)
        series = self._series()
        _, weeks = self._plan(series)
        on_day = [x for w in weeks for x in w["sessions"] if x[0] == day]
        if not 0 <= int(k) < len(on_day):
            return None
        s = on_day[int(k)]
        if s[1] in ("Race", "Rest"):
            return None
        if isinstance(s[5], str):
            return self.session_brief(s[5][2:])
        sc = dict(
            uid=None, date=date, time=session_time(P, s), sport=s[1], kind=kind_of(s), dur_s=s[2], dist_km=0.0, notes=""
        )
        ready = (
            readiness(self._wellness(), series[-1][3], active_on(self._issues(), dt.date.today()))[0]
            if day <= dt.date.today() + ONE
            else None
        )
        out = session_brief(P, sc, self._wx, series[-1][3], ready, active_on(self._issues(), day))
        out.update(
            place=P["home_place"],
            title=f"{s[1]}" + (f" · {P.get('team_label') or TEAM_TAG}" if is_team(s) else f" · {sc['kind'].lower()}"),
            detail=s[4],
            plan=True,
        )
        return out

    @_locked
    def set_weather(self, wx):
        """Keep the latest forecast, and record the conditions on recent outdoor workouts that don't have them yet."""
        if not (wx or {}).get("hourly", {}).get("time"):
            return dict(ok=False, stamped=0)
        self._wx = {"hourly": wx["hourly"]}
        return dict(ok=True, stamped=self._stamp_weather())

    def _stamp_weather(self):
        first = self._wx["hourly"]["time"][0][:10]
        n = 0
        for w in self._db.execute(
            "SELECT * FROM workouts WHERE wx_temp IS NULL AND NOT COALESCE(indoor, 0) AND date >= ? " "AND date <= ?",
            (first, dt.date.today().isoformat()),
        ).fetchall():
            if w["sport"] not in OUTDOOR:
                continue
            day = dt.date.fromisoformat(w["date"])
            team = P.get("team_on") and day.weekday() in P.get("team_days", []) and w["sport"] == P.get("team_sport")
            start = (
                dt.datetime.fromisoformat(w["start"])
                if w["start"]
                else at(day, P["team_time"] if team else P["train_time"])
            )
            c = wx_during(self._wx, start, start + dt.timedelta(seconds=w["dur_s"] or 3600))
            if c and c["dew"] is not None:
                self._db.execute(
                    "UPDATE workouts SET wx_temp=?, wx_dew=?, wx_code=? WHERE id=?",
                    (round(c["temp_max"], 1), round(c["dew"], 1), c["code"], w["id"]),
                )
                n += 1
        self._db.commit()
        return n

    @_locked
    def set_location(self, place, lat, lon):
        P.update(home_place=str(place or "")[:80], home_lat=float(lat or 0), home_lon=float(lon or 0))
        self._save()
        return dict(ok=True)

    @_locked
    def toggle_habit(self, uid, date, done):
        self._db.execute(
            "INSERT OR REPLACE INTO habit_log(hkey, habit, date, done) VALUES(?,?,?,?)",
            (f"{uid}:{date}", uid, date, 1 if done else 0),
        )
        self._db.commit()
        return dict(ok=True)

    @_locked
    def save_habit(self, f):
        name = (f.get("name") or "").strip()
        days = sorted({int(x) for x in f.get("days") or [] if 0 <= int(x) <= 6})
        if not name or not days:
            return dict(ok=False, error="Give it a name and at least one day")
        if f.get("uid"):
            self._db.execute("UPDATE habits SET name=?, days=? WHERE uid=?", (name, json.dumps(days), f["uid"]))
        else:
            n = self._db.execute("SELECT COALESCE(MAX(sort), 0) + 1 FROM habits").fetchone()[0]
            self._db.execute("INSERT INTO habits(name, days, sort) VALUES(?,?,?)", (name, json.dumps(days), n))
        self._db.commit()
        return dict(ok=True)

    @_locked
    def delete_habit(self, uid):
        return self._take("habits", "uid", [uid])

    @_locked
    def save_reminder(self, f):
        try:
            h, m = clock(f.get("time") or "")
        except (ValueError, TypeError):
            return dict(ok=False, error="Pick a time")
        title = (f.get("title") or "").strip()
        days = sorted({int(x) for x in f.get("days") or [] if 0 <= int(x) <= 6})
        if not title or not days:
            return dict(ok=False, error="Give it a title and at least one day")
        rec = (title, f"{h:02d}:{m:02d}", json.dumps(days), 0 if f.get("active") is False else 1)
        if f.get("uid"):
            self._db.execute("UPDATE reminders SET title=?, time=?, days=?, active=? WHERE uid=?", rec + (f["uid"],))
        else:
            self._db.execute("INSERT INTO reminders(title, time, days, active) VALUES(?,?,?,?)", rec)
        self._db.commit()
        return dict(ok=True)

    @_locked
    def delete_reminder(self, uid):
        return self._take("reminders", "uid", [uid])

    @_locked
    def save_quote(self, f):
        text = (f.get("text") or "").strip().strip('"“”').strip()
        if not text:
            return dict(ok=False, error="Type the quote")
        self._db.execute(
            "INSERT INTO quotes(text, author) VALUES(?,?)", (text, (f.get("author") or "").strip() or "Unknown")
        )
        self._db.commit()
        return dict(ok=True)

    @_locked
    def delete_quote(self, uid):
        return self._take("quotes", "uid", [uid])

    @_locked
    def notification_plan(self, days=7, wx=None):
        wx = wx or self._wx
        """Local notifications for the next `days` days (the phone schedules them; iOS allows 64 pending)."""
        now = dt.datetime.now()
        today = now.date()
        weeks = self._plan()[1]
        out = []
        reminders = [r for r in self._db.execute("SELECT * FROM reminders WHERE active")]
        for k in range(days + 1):
            day = today + dt.timedelta(days=k)
            if P["notify_bedtime"]:
                bt = bedtime_before(P, day + ONE)
                when = bt - dt.timedelta(minutes=int(P["winddown"] or 0))
                out.append(
                    dict(
                        id=1000 + k,
                        at=when,
                        title="Time to wind down",
                        body=f"Lights out by {fmt12(bt)} for {sleep_goal(P):g} h before your {fmt12(wake_on(P, day + ONE))} "
                        f"wake-up. Screens away, room cool and dark.",
                    )
                )
            if P["notify_checkin"]:
                out.append(
                    dict(
                        id=2000 + k,
                        at=at(day, P["checkin_time"]),
                        title="Morning check-in",
                        body="20 seconds: how you slept, soreness and energy. It shapes today's plan.",
                    )
                )
            if P["notify_nudge"]:
                items = self._open_items(day, weeks)
                q = self._quote_for(day, 1)
                if items and q:
                    title = (
                        f"Still to do: {', '.join(items[:2])}" + (f" +{len(items) - 2} more" if len(items) > 2 else "")
                        if k == 0
                        else "Anything left on today's list?"
                    )
                    out.append(
                        dict(
                            id=3000 + k,
                            at=at(day, P["nudge_time"]),
                            title=title,
                            body=f"\u201c{q['text']}\u201d \u2014 {q['author']}",
                        )
                    )
            for i, r in enumerate(reminders):
                if day.weekday() in json.loads(r["days"]):
                    out.append(dict(id=10000 + i * 10 + k, at=at(day, r["time"]), title=r["title"], body="Reminder"))
        if (
            int(P.get("brief_min") or 0) > 0
        ):  # briefing before each scheduled session: weather, what to wear, what to bring
            for i, sc in enumerate(
                x
                for x in self._scheduled()
                if today.isoformat() <= x["date"] <= (today + dt.timedelta(days=days)).isoformat()
            ):
                b = session_brief(P, sc, wx, 0, None, [])
                start = at(dt.date.fromisoformat(sc["date"]), sc["time"])
                w = b["weather"]
                title = f"{b['title']} at {fmt12(start)}" + (f" · {w['temp']}, {w['sky'].lower()}" if w else "")
                body = ". ".join(
                    x
                    for x in (
                        ("Wear: " + ", ".join(b["wear"][:4]).lower()) if b["wear"] else "",
                        ("Bring: " + ", ".join(b["bring"][:3]).lower()) if b["bring"] else "",
                        f"Target {b['pace']}" if b["pace"] else "",
                        *b["advice"][:1],
                    )
                    if x
                )
                out.append(
                    dict(
                        id=20000 + i, at=start - dt.timedelta(minutes=int(P["brief_min"])), title=title, body=body + "."
                    )
                )
        for i, r in enumerate(
            x for x in self._races() if today.isoformat() <= x["date"] <= (today + dt.timedelta(days=days)).isoformat()
        ):
            start = at(dt.date.fromisoformat(r["date"]), r["start"])
            pr = predict(P, r, self._series()[-1][1])
            fuel = race_fueling(P, r, pr)["timeline"]
            breakfast = next((x["detail"] for x in fuel if x["what"] == "Breakfast"), "")
            w = r.get("wx")
            wear = what_to_wear(r["legs"][0]["sport"], "Race pace", w) if w else []
            body = ". ".join(
                x
                for x in (
                    f"Breakfast now: {breakfast.split('.')[0]}" if breakfast else "",
                    ("Wear: " + ", ".join(wear[:4]).lower()) if wear else "",
                    f"Predicted {hms(pr['total'])}" if pr["total"] else "",
                )
                if x
            )
            out.append(
                dict(
                    id=30000 + i,
                    at=start - dt.timedelta(hours=3),
                    title=f"Race day: {r['name']} at {fmt12(start)}" + (f" · {wx_short(w)}" if w else ""),
                    body=body + ".",
                )
            )
        out = sorted((n for n in out if n["at"] > now), key=lambda n: n["at"])[:60]
        return [dict(n, at=n["at"].isoformat(timespec="minutes")) for n in out]

    # ---- Apple Health (phone): the bridge reads HealthKit, this merges it
    @_locked
    def import_health(self, workouts, samples):
        acts, daily = health_to_data(workouts or [], samples or [])
        added, dups = self._import_activities(acts)
        days = 0
        cols = ("rhr", "hrv", "sleep_h", "weight_kg")
        for d, vals in sorted(daily.items()):
            row = self._db.execute("SELECT * FROM wellness WHERE date=?", (d,)).fetchone()
            if not row:
                self._db.execute(
                    "INSERT INTO wellness(date, rhr, hrv, sleep_h, weight_kg) VALUES(?,?,?,?,?)",
                    (d, *(vals[c] for c in cols)),
                )
                days += 1
            else:  # only fill what the athlete left blank; typed-in values always win
                fill = {c: vals[c] for c in cols if row[c] is None and vals[c] is not None}
                if fill:
                    self._db.execute(
                        f"UPDATE wellness SET {', '.join(f'{c}=?' for c in fill)} WHERE date=?", (*fill.values(), d)
                    )
                    days += 1
        latest = self._db.execute(
            "SELECT weight_kg FROM wellness WHERE weight_kg IS NOT NULL ORDER BY date DESC LIMIT 1"
        ).fetchone()
        if latest and abs(latest[0] - P["weight_kg"]) > 0.05:
            P["weight_kg"] = round(latest[0], 2)
            self._save()
        P["health_last"] = dt.datetime.now().isoformat(timespec="seconds")
        save_profile(self._db, touch=False)
        self._db.commit()
        return dict(ok=True, added=added, skipped=len(dups), days=days)

    @_locked
    def health_state(self):
        return dict(on=P["health_on"], last=P["health_last"])

    @_locked
    def health_rescan(self):
        """Forget when Health was last read, so the next import looks back the full 90 days. Duplicates are skipped."""
        P["health_last"] = ""
        save_profile(self._db, touch=False)
        return dict(ok=True)

    @_locked
    def health_enable(self, on):
        P["health_on"] = bool(on)
        save_profile(self._db, touch=False)
        return dict(ok=True)

    # ---- file transfer without native dialogs (phone)
    @_locked
    def import_texts(self, files):
        import tempfile

        folder = tempfile.mkdtemp()
        paths = []
        for f in files:
            path = os.path.join(folder, os.path.basename(f["name"]))
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(f["text"])
            paths.append(path)
        return self._import_paths(paths)

    @_locked
    def export_all_text(self):
        return json.dumps(
            dict(
                version=4,
                exported=dt.datetime.now().isoformat(timespec="seconds"),
                profile=P,
                **{t: [dict(r) for r in self._db.execute(f"SELECT * FROM {t}")] for t in DATA_TABLES},
            ),
            indent=1,
        )

    @_locked
    def restore_text(self, text):
        return self._restore(json.loads(text))

    # ---- zones & tests
    @_locked
    def zones(self):
        return dict(groups=zones(P), sports=self._sports(), dist_unit=unit("dist"), swim_unit="yd" if imp() else "m")

    # ---- records & ranks
    @_locked
    def records(self):
        return records(self._workouts(), self._races(forecast=False), P)

    @_locked
    def estimate(self, f):
        """A predicted time for any distance or event: the same model the race predictions use, at today's fitness."""
        try:
            legs = [
                dict(
                    sport=l["sport"], km=leg_dist_from(l["sport"], l["dist"]), elev=from_ui("elev", l.get("elev") or 0)
                )
                for l in f.get("legs") or []
            ]
            if not legs or any(l["sport"] not in LEG_SPORTS or l["km"] <= 0 for l in legs):
                raise ValueError("Every leg needs a distance")
            temp = from_ui("temp", f.get("temp") or to_ui("temp", 18))
        except (ValueError, KeyError, TypeError):
            return dict(ok=False, error="Check the distances")
        race = dict(
            legs=legs, temp_c=temp, t1=parse_clock(f.get("t1") or "3:00"), t2=parse_clock(f.get("t2") or "2:00")
        )
        pr = predict(P, race, self._series()[-1][1])
        total, source = pr["total"], "model"
        if not pr["modelled"]:
            total, source = None, ""
            if len(legs) == 1:
                total = log_estimate(self._workouts(), legs[0]["sport"], legs[0]["km"])
                source = "log" if total else ""
        rows = []
        for sg in pr["segs"]:
            if sg["kind"] == "trans":
                rows.append(dict(sport=sg["sport"], label=sg["sport"], time=hms(sg["secs"]), pace="", trans=True))
            else:
                t = sg["secs"] or (total if len(legs) == 1 else None)
                rows.append(
                    dict(
                        sport=sg["sport"],
                        label=leg_label(sg["sport"], sg["km"]),
                        time=hms(t) if t else "",
                        pace=sg["pace"]
                        or (event_pace(sg["sport"], t, sg["km"]) if t and sg["sport"] in ("Row", "Ski") else ""),
                    )
                )
        rank = (
            leg_rank(P, legs[0]["sport"], legs[0]["km"], total)
            if len(legs) == 1 and total and legs[0]["sport"] in ("Swim", "Bike", "Run", "Row")
            else None
        )
        return dict(
            ok=True,
            total=hms(total) if total else "",
            lo=hms(total * 0.96) if total else "",
            hi=hms(total * 1.05) if total else "",
            source=source,
            segs=rows,
            rank=rank,
            modelled=pr["modelled"],
            ctl=round(self._series()[-1][1]),
        )

    @_locked
    def apply_test(self, kind, v):
        try:
            if kind == "ftp":
                upd = {"ftp": round(float(v[0]) * 0.95)}
            elif kind == "lthr":
                upd = {"lthr": float(v[0])}
            elif kind == "maxhr":
                upd = {"max_hr": float(v[0])}
            elif kind == "css":
                upd = {"css": (parse_clock(v[0]) - parse_clock(v[1])) / 2 / (YD if imp() else 1)}
            else:
                d, t = from_ui("dist", v[0]), parse_clock(v[1])
                upd = {"run_thr_pace": threshold_from_race(d, t), "recent_race_km": d, "recent_race_s": t}
            if any(not x > 0 for x in upd.values()):
                raise ValueError("Result must be positive")
        except (ValueError, ZeroDivisionError, IndexError) as e:
            return dict(ok=False, error=str(e) or "Check the inputs")
        P.update(upd)
        self._save()
        show = {
            "ftp": lambda x: f"FTP {x:.0f} W",
            "lthr": lambda x: f"LTHR {x:.0f} bpm",
            "max_hr": lambda x: f"Max HR {x:.0f}",
            "css": lambda x: f"CSS {fd('swim', x)}",
            "run_thr_pace": lambda x: f"Threshold {fd('pace', x)}",
        }
        return dict(ok=True, msg=", ".join(show[k](x) for k, x in upd.items() if k in show))

    # ---- profile
    def _profile_value(self, k, kind):
        v = P[k]
        if isinstance(kind, tuple) or kind in ("str", "date", "bool", "sports", "weekdays", "clock"):
            return v
        return to_ui(kind, v)

    def _fields(self, keys):
        races = [r for r in self._races() if dt.date.fromisoformat(r["date"]) >= dt.date.today()]
        fields = []
        for k in keys:
            label, kind, hlp = PROFILE_META[k]
            if k == "plan_race":
                kind = (
                    "select",
                    [("", "Auto")] + [(r["uid"], f"{r['name']} ({r['priority']}) · {r['date']}") for r in races],
                )
            sel = isinstance(kind, tuple)
            fields.append(
                dict(
                    key=k,
                    label=label,
                    kind="select" if sel else kind,
                    help=hlp,
                    options=[[str(a), b] for a, b in kind[1]] if sel else None,
                    unit=unit(kind) if not sel else "",
                    value=str(P[k]) if sel else self._profile_value(k, kind),
                )
            )
        return fields

    @_locked
    def profile(self):
        races = [r for r in self._races() if dt.date.fromisoformat(r["date"]) >= dt.date.today()]
        secs = []
        for title, keys in PROFILE_SECTIONS:
            fields = []
            for k in keys:
                label, kind, hlp = PROFILE_META[k]
                if k == "plan_race":
                    kind = (
                        "select",
                        [("", "Auto")] + [(r["uid"], f"{r['name']} ({r['priority']}) · {r['date']}") for r in races],
                    )
                sel = isinstance(kind, tuple)
                fields.append(
                    dict(
                        key=k,
                        label=label,
                        kind="select" if sel else kind,
                        help=hlp,
                        options=[[str(a), b] for a, b in kind[1]] if sel else None,
                        unit=unit(kind) if not sel else "",
                        value=str(P[k]) if sel else self._profile_value(k, kind),
                    )
                )
            secs.append(dict(title=title, fields=fields))
        return dict(sections=secs, all_sports=ALL_SPORTS)

    @_locked
    def save_profile(self, vals):
        upd = {}
        for k, s in vals.items():
            if k == "units" or k not in PROFILE_META:
                continue
            label, kind, _ = PROFILE_META[k]
            try:
                if kind == "bool":
                    upd[k] = bool(s)
                elif kind == "sports":
                    upd[k] = [x for x in ALL_SPORTS if x in (s or [])]
                    if not upd[k]:
                        return dict(ok=False, error="Pick at least one discipline", field=k)
                elif kind == "weekdays":
                    upd[k] = sorted({int(x) for x in (s or []) if 0 <= int(x) <= 6})
                elif kind == "clock":
                    h, m = clock(s)
                    upd[k] = f"{h:02d}:{m:02d}"
                elif isinstance(kind, tuple) or k == "plan_race":
                    upd[k] = type(DEFAULTS[k])(s)
                elif str(s).strip() == self._profile_value(k, kind):
                    continue  # unchanged: don't round-trip through display rounding
                else:
                    upd[k] = from_ui(kind, s)
            except (ValueError, TypeError):
                return dict(ok=False, error=f"{label}: invalid value", field=k)
        for k in ("ftp", "lthr", "run_thr_pace", "css", "weight_kg", "height_cm", "cda", "max_hr"):
            if k in upd and not upd[k] > 0:
                return dict(ok=False, error=f"{PROFILE_META[k][0]} must be greater than 0", field=k)
        P.update(upd)
        P["units"] = vals.get("units", P["units"])
        self._save()
        return dict(ok=True)

    # ---- data safety
    @_locked
    def data_info(self):
        folder = os.path.join(os.path.dirname(self._path), "backups") if self._path != ":memory:" else ""
        backups = sorted(glob.glob(os.path.join(folder, "data-*.db"))) if folder else []
        saved = self._db.execute("SELECT v FROM kv WHERE k='saved_at'").fetchone()
        count = lambda t: self._db.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0]
        return dict(
            path=self._path,
            folder=os.path.dirname(self._path),
            saved_at=saved["v"] if saved else None,
            backups=len(backups),
            last_backup=os.path.basename(backups[-1]) if backups else None,
            counts=dict(workouts=count("workouts"), races=count("races"), wellness=count("wellness")),
        )

    def open_data_folder(self):
        os.startfile(os.path.dirname(self._path))

    def export_all(self):
        path = self._save_dialog(f"endurance-coach-{dt.date.today()}.json", ("JSON (*.json)",))
        if not path:
            return dict(cancelled=True)
        with self._lock:
            data = dict(
                version=3,
                exported=dt.datetime.now().isoformat(timespec="seconds"),
                profile=P,
                **{t: [dict(r) for r in self._db.execute(f"SELECT * FROM {t}")] for t in DATA_TABLES},
            )
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(data, fh, indent=1)
        return dict(path=path)

    def import_all(self):
        import webview

        paths = self._window.create_file_dialog(webview.FileDialog.OPEN, file_types=("JSON (*.json)",))
        if not paths:
            return dict(cancelled=True)
        with open(paths[0], encoding="utf-8") as fh:
            data = json.load(fh)
        with self._lock:
            return self._restore(data)

    def _restore(self, data):
        if not isinstance(data, dict) or "profile" not in data:
            return dict(ok=False, error="Not an Endurance Coach export")
        if self._path != ":memory:":
            backup_db(self._path)  # snapshot before replacing anything
        db = self._db
        with db:
            for t in DATA_TABLES:
                db.execute(f"DELETE FROM {t}")
                for r in data.get(t, []):
                    db.execute(
                        f"INSERT INTO {t}({','.join(f'"{c}"' for c in r)}) VALUES({','.join('?' * len(r))})",
                        list(r.values()),
                    )
            db.execute("INSERT OR REPLACE INTO kv VALUES('profile', ?)", (json.dumps(data["profile"]),))
            for t in SYNC_TABLES:  # re-stamp everything so a restore propagates to paired devices
                db.execute(f"UPDATE {t} SET updated=NULL")
        load_profile(db)
        save_profile(db)
        return dict(ok=True, counts={t: len(data.get(t, [])) for t in DATA_TABLES})


def threshold_from_race(km, secs):
    """~1-hour pace (s/km) from any recent all-out run race, by inverting Riegel."""
    return 3600 / (km * (3600 / secs) ** (1 / 1.06))


def _zc_name(name):
    """A service instance name mDNS will accept, derived from what the user called this device."""
    import re

    clean = re.sub(r"[^A-Za-z0-9 _-]", "", str(name or "")).strip()[:40]
    return f"{clean or APP}.{SERVICE_TYPE}"


def advertise_hub(port, name):
    """Publish this hub on the local network. Returns a handle to stop with, or None if mDNS is unavailable -
    in which case nothing breaks, clients just fall back to searching the hard way."""
    try:
        from zeroconf import ServiceInfo, Zeroconf
    except ImportError:
        return None
    import socket

    addrs = [socket.inet_aton(ip) for ip in lan_addresses()]
    if not addrs:
        return None
    try:
        zc = Zeroconf()
        info = ServiceInfo(
            SERVICE_TYPE,
            _zc_name(name),
            addresses=addrs,
            port=port,
            properties={"app": APP, "name": str(name or "")[:40]},
        )
        zc.register_service(info, allow_name_change=True)  # two PCs can share a name; mDNS renames the second
        return (zc, info)
    except OSError:
        return None


def stop_advertising(handle):
    if not handle:
        return
    zc, info = handle
    try:
        zc.unregister_service(info)
    except (OSError, RuntimeError):
        pass
    zc.close()


def browse_hubs(timeout=2.5):
    """Hubs advertising themselves right now, as [(host:port, device name)]. Empty when mDNS is unavailable or
    the network drops multicast, which is exactly when the sweep earns its keep."""
    try:
        from zeroconf import ServiceBrowser, Zeroconf
    except ImportError:
        return []
    import socket

    found = {}

    class Listener:
        def add_service(self, zc, type_, name):
            info = zc.get_service_info(type_, name, timeout=1500)
            if not info or not info.port:
                return
            label = (info.properties or {}).get(b"name", b"").decode("utf-8", "replace")
            for raw in info.addresses:
                try:
                    found[f"{socket.inet_ntoa(raw)}:{info.port}"] = label or name.split(".")[0]
                except OSError:
                    pass

        def update_service(self, *a):
            pass

        def remove_service(self, *a):
            pass

    try:
        zc = Zeroconf()
    except OSError:
        return []
    try:
        ServiceBrowser(zc, SERVICE_TYPE, Listener())
        time.sleep(timeout)
    finally:
        zc.close()
    return sorted(found.items())


def device_label():
    if IS_PHONE:
        return "iPhone"
    import socket

    try:
        return socket.gethostname().split(".")[0] or "This PC"
    except OSError:
        return "This PC"


def this_device(p):
    """Stable id and label for this install so a hub can list what syncs with it. Both are LOCAL_KEYS - if they
    synced, every device would end up claiming to be the same one."""
    if not p.get("device_id"):
        import secrets

        p["device_id"] = secrets.token_hex(6)
    if not p.get("device_name"):
        p["device_name"] = device_label()
    return dict(id=p["device_id"], name=p["device_name"], kind="phone" if IS_PHONE else "computer")


def post_sync(host, code, body, timeout=20):
    """One exchange with a hub. Returns (status, payload); status is None when nothing answered."""
    import urllib.error
    import urllib.request

    req = urllib.request.Request(
        f"http://{host}/sync",
        data=json.dumps(body).encode(),
        headers={"Content-Type": "application/json", "X-Sync-Code": code},
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.status, json.loads(r.read() or b"{}")
    except urllib.error.HTTPError as e:
        try:
            return e.code, json.loads(e.read() or b"{}")
        except ValueError:
            return e.code, {}
    except (urllib.error.URLError, OSError, ValueError):
        return None, {}


def probe_hub(host, code, timeout=0.8):
    """'hit' when one of our hubs answers, 'alive' when any machine does, 'dead' when nothing is there."""
    import urllib.error
    import urllib.request

    t0 = time.time()
    req = urllib.request.Request(f"http://{host}/hello", headers={"X-Sync-Code": code})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return "hit" if json.loads(r.read() or b"{}").get("app") == APP else "alive"
    except urllib.error.HTTPError:
        return "alive"  # something answered - wrong code, or not us
    except (urllib.error.URLError, OSError, ValueError):
        return "alive" if time.time() - t0 < timeout * 0.75 else "dead"  # refused fast = a machine is there


def discover_hub(last_host, code, budget=30):
    """Find the hub again after the router moved it. Sweeps the saved machine's other ports, then our own /24s
    nearest-first, then the other ports of whatever answered.
    ponytail: a plain /24 sweep, same as the phone's; mDNS would be tidier but needs a dependency."""
    from concurrent.futures import ThreadPoolExecutor

    ip = (last_host or "").split(":")[0]
    known = ip.count(".") == 3 and all(part.isdigit() for part in ip.split("."))
    end, alive, found = time.time() + budget, set(), []
    for host, _name in (browse_hubs(min(2.5, budget)) if budget > 0 else []):
        if time.time() >= end:  # ask the network who is there before guessing at addresses
            return None
        if probe_hub(host, code) == "hit":
            return host

    def sweep(hosts):
        def probe(h):
            # Windows' clock ticks about every 15 ms, so a zero budget lands on exactly `end` rather than past
            # it - compare inclusively or a caller asking for no sweep still gets one.
            if found or time.time() >= end:  # someone already hit, or we are out of time: stop paying for probes
                return
            r = probe_hub(h, code)
            if r == "hit":
                found.append(h)
            elif r == "alive":
                alive.add(h.split(":")[0])

        with ThreadPoolExecutor(max_workers=48) as pool:
            list(pool.map(probe, hosts))
        return found[0] if found else None

    if known and (hit := sweep([f"{ip}:{p}" for p in SYNC_PORTS])):
        return hit
    bases = [ip.rsplit(".", 1)[0]] if known else sorted({a.rsplit(".", 1)[0] for a in lan_addresses()})
    last = int(ip.rsplit(".", 1)[1]) if known else 0
    for base in bases:
        order = sorted(range(1, 255), key=lambda i: abs(i - last)) if last else list(range(1, 255))
        if hit := sweep([f"{base}.{i}:{SYNC_PORTS[0]}" for i in order if f"{base}.{i}" != ip]):
            return hit
    if known:
        alive.add(ip)
    return sweep([f"{h}:{p}" for h in sorted(alive) for p in SYNC_PORTS[1:]]) if alive else None


def asset_bytes(name):
    """One servable asset, or None. Only the two names above, and only from where this copy of the app lives."""
    if name not in ASSET_FILES:
        return None
    try:
        with open(resource(name), "rb") as fh:
            return fh.read()
    except OSError:
        return None  # endurance.py is absent from an exe built before --add-data included it


def asset_manifest():
    """What this device can hand over, with a digest per file so the phone re-downloads only what changed."""
    out = {}
    for name in ASSET_FILES:
        raw = asset_bytes(name)
        if raw is not None:
            out[name] = dict(size=len(raw), digest=hashlib.sha256(raw).hexdigest()[:16])
    return dict(app=APP, version=VERSION, name=P["name"], device=P.get("device_name") or device_label(), files=out)


def start_hub(api, port=8977):
    """Tiny HTTP server on the LAN so the other devices - a second computer, a phone - can sync with this one.
    Every request needs the pairing code; repeated wrong codes lock that address out for a minute."""
    import hmac
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

    fails = {}

    class Hub(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def _send(self, code, obj=None):
            body = json.dumps(obj).encode() if obj is not None else b""
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Headers", "Content-Type, X-Sync-Code")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def _authorised(self):
            ip = self.client_address[0]
            count, until = fails.get(ip, (0, 0))
            if time.time() < until:
                self._send(429, dict(error="Too many wrong codes. Wait a minute."))
                return False
            given = (self.headers.get("X-Sync-Code") or "").upper().replace("-", "")
            if P["hub_code"] and hmac.compare_digest(given, P["hub_code"].replace("-", "")):
                fails.pop(ip, None)
                return True
            count += 1
            fails[ip] = (count, time.time() + 60 if count >= 5 else 0)
            self._send(401, dict(error="Wrong pairing code"))
            return False

        def do_OPTIONS(self):
            self._send(204)

        def _send_file(self, raw, kind):
            self.send_response(200)
            self.send_header("Content-Type", kind)
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)

        def do_GET(self):
            route = self.path.split("?")[0]
            if route == "/hello":
                if self._authorised():
                    self._send(200, dict(app=APP, name=P["name"], serves_assets=bool(P.get("serve_assets"))))
            elif route == "/assets" or route.startswith("/assets/"):
                if not self._authorised():
                    return
                if not P.get("serve_assets"):
                    return self._send(403, dict(error="This device is not set up to hand over its app files."))
                if route == "/assets":
                    return self._send(200, asset_manifest())
                raw = asset_bytes(route[len("/assets/") :])
                if raw is None:
                    return self._send(404, dict(error="not an app file this device can hand over"))
                self._send_file(raw, "text/plain; charset=utf-8")
            else:
                self._send(404, dict(error="not found"))

        def do_POST(self):
            if self.path != "/sync":
                return self._send(404, dict(error="not found"))
            if not self._authorised():
                return
            size = int(self.headers.get("Content-Length") or 0)
            if size > 50 * 1024 * 1024:
                return self._send(413, dict(error="too large"))
            try:
                self._send(200, api.hub_exchange(json.loads(self.rfile.read(size) or b"{}")))
            except (ValueError, KeyError, TypeError) as e:
                self._send(400, dict(error=str(e)))

    class Server(ThreadingHTTPServer):
        # never share a port: Windows' SO_REUSEADDR would let a second hub bind a port already in use,
        # and phones would then reach whichever process answers first
        allow_reuse_address = False

        def server_bind(self):
            import socket

            if hasattr(socket, "SO_EXCLUSIVEADDRUSE"):
                self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
            super().server_bind()

    for p_ in range(port, port + 10):
        try:
            srv = Server(("0.0.0.0", p_), Hub)
            break
        except OSError:
            continue
    else:
        raise OSError("No free port for device sync")
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    srv.mdns = advertise_hub(srv.server_address[1], P.get("device_name") or device_label())
    return srv


def version_tuple(v):
    """'v1.2.3' -> (1, 2, 3). Anything unparseable sorts lowest so a bad tag never looks like an upgrade."""
    parts = re.findall(r"\d+", str(v or ""))
    return tuple(int(x) for x in parts[:4]) or (0,)


def frozen_exe():
    """The running exe when packaged by PyInstaller, else None - a dev checkout has nothing to replace."""
    return os.path.abspath(sys.executable) if getattr(sys, "frozen", False) else None


def clear_old_build():
    """Delete the previous exe left behind by an update. Called once at startup, when it is no longer running."""
    exe = frozen_exe()
    for stale in glob.glob(exe + ".old-*") if exe else []:
        try:
            os.remove(stale)
        except OSError:
            pass  # still locked, or already gone; it will be caught next launch


def check_for_update(timeout=8):
    """Ask GitHub what the newest release is. Reports only - it downloads nothing."""
    import urllib.error
    import urllib.request

    req = urllib.request.Request(
        RELEASES_API, headers={"Accept": "application/vnd.github+json", "User-Agent": f"{APP}/{VERSION}"}
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            rel = json.loads(r.read())
    except Exception as e:  # noqa: BLE001 - a background check must never surface as a crash, whatever broke
        return dict(ok=False, error=f"Couldn't reach GitHub: {e}")
    tag = rel.get("tag_name") or ""
    asset = next((a for a in rel.get("assets") or [] if a.get("name") == ASSET_NAME), None)
    return dict(
        ok=True,
        current=VERSION,
        latest=tag.lstrip("v"),
        tag=tag,
        newer=version_tuple(tag) > version_tuple(VERSION),
        notes=(rel.get("body") or "").strip()[:2000],
        url=rel.get("html_url") or "",
        size=asset.get("size") if asset else None,
        download=asset.get("browser_download_url") if asset else None,
        installable=bool(asset) and bool(frozen_exe()),
    )


def install_update(url, expect_size=None, timeout=300):
    """Download the release exe and put it where the running one is. Returns the path that will run next time.

    Deliberately never launches anything: the app asks to be restarted, and the athlete restarts it.
    """
    import urllib.error
    import urllib.request

    exe = frozen_exe()
    if not exe:
        return dict(ok=False, error="This looks like a source checkout, so there is no exe to replace.")
    if not str(url).startswith(f"https://github.com/{UPDATE_REPO}/releases/download/"):
        return dict(ok=False, error="That download does not come from this app's releases.")
    fresh = exe + ".new"
    try:
        req = urllib.request.Request(url, headers={"User-Agent": f"{APP}/{VERSION}"})
        with urllib.request.urlopen(req, timeout=timeout) as r, open(fresh, "wb") as fh:
            shutil.copyfileobj(r, fh)
    except (urllib.error.URLError, OSError) as e:
        _quietly_remove(fresh)
        return dict(ok=False, error=f"Download failed: {e}")
    size = os.path.getsize(fresh)
    if size < 5_000_000 or (expect_size and abs(size - expect_size) > 1024):
        _quietly_remove(fresh)
        return dict(ok=False, error="The download was incomplete. Nothing has been changed.")
    old = f"{exe}.old-{int(time.time())}"
    try:
        os.replace(exe, old)  # renaming a running exe is allowed on Windows; overwriting it is not
        os.replace(fresh, exe)
    except OSError as e:
        if os.path.exists(old) and not os.path.exists(exe):
            os.replace(old, exe)  # put it back rather than leave the app with no exe at all
        _quietly_remove(fresh)
        return dict(ok=False, error=f"Could not replace the app: {e}")
    return dict(ok=True, restart=True)


def _quietly_remove(path):
    try:
        os.remove(path)
    except OSError:
        pass


def resource(name):
    return os.path.join(getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__))), name)


def dark_theme():
    """Resolve the theme setting; 'system' follows the Windows app theme."""
    if P.get("theme") in ("light", "dark"):
        return P["theme"] == "dark"
    try:
        import winreg

        key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
        return winreg.QueryValueEx(key, "AppsUseLightTheme")[0] == 0
    except OSError:
        return False


def run_app():
    import webview

    clear_old_build()  # the exe this one replaced, now that it is no longer running
    api = Api()
    with open(resource("ui.html"), encoding="utf-8") as fh:
        html = fh.read()
    if P.get("hub_on"):
        try:
            api.hub_set(True)
        except OSError:
            P["hub_on"] = False
    api._window = webview.create_window(
        APP,
        html=html,
        js_api=api,
        min_size=(1100, 700),
        maximized=True,
        background_color="#0e1013" if dark_theme() else "#f5f6f8",
    )
    webview.start()


# ---------------------------------------------------------------- self-test

# ---------------------------------------------------------------- self-test


def selftest():
    """Run the suite from ectests.py. Imported here rather than at module scope so the engine the phone
    downloads, and the packaged exe, carry none of it."""
    import ectests

    ectests.selftest()


if __name__ == "__main__":
    selftest() if "--selftest" in sys.argv else run_app()
