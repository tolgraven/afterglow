"""Render a still and a slow-motion timeline from recorded scheduler events."""

import json
import subprocess
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

HERE = Path(__file__).resolve().parent
WIDTH, HEIGHT = 1280, 720
FONTS = Path("/usr/share/fonts/truetype/dejavu")
BACKGROUND = "#0e1826"
SURFACE = "#162438"
WHITE = "#eaf1f7"
MUTED = "#a6b8cc"
GRID = "#3b516a"
TEAL = "#76e3cd"
AMBER = "#ffcc83"

FONT = {}
for size, face in [(14, "SansMono"), (17, "Sans"), (18, "SansMono"), (19, "Sans"), (22, "Sans"), (24, "Sans-Bold"), (46, "Sans-Bold")]:
    FONT[size] = ImageFont.truetype(str(FONTS / ("DejaVu" + face + ".ttf")), size)


def events(filename):
    trace = json.loads((HERE / filename).read_text())
    return next(case["events"] for case in trace if case["scenario"] == "recover")


RELEASED = events("released-4f65f06c.json")
CANDIDATE = events("candidate.json")
FIRST_HANDOFF = next(item for item in CANDIDATE if "timing" in item)["timing"]
GUARD_START = FIRST_HANDOFF["sent-by-ms"]
GUARD_END = next(item["due-next-ms"] for item in CANDIDATE if item["event"] == "status")
RELEASED_WAKE = next(item["due-next-ms"] for item in RELEASED if item["event"] == "status")
RECOVERED = next(item for item in CANDIDATE if item["event"] == "artdmx" and item["frame-id"] == 2)
assert GUARD_END == RECOVERED["at-ms"] == 57.5
assert RELEASED_WAKE == 75.0
assert FIRST_HANDOFF["sent-at-ms"] == 44.0


def point(ms):
    return 354 + ((ms - 25) / 78) * 815


def label(draw, pos, text, size=17, fill=WHITE, anchor=None):
    draw.text(pos, text, fill, font=FONT[size], anchor=anchor)


def marker(draw, at_ms, y, rgb, accent, fresh):
    x = point(at_ms)
    draw.ellipse((x - 8, y - 8, x + 8, y + 8), fill=accent if fresh else SURFACE, outline=accent, width=2)
    label(draw, (x, y - 18), f"{at_ms:g} ms", 18, accent, "ms")
    label(draw, (x, y + 20), f"R={rgb[0]}", 14, MUTED, "mt")


def make_frame(now, step, still=False):
    image = Image.new("RGB", (WIDTH, HEIGHT), BACKGROUND)
    draw = ImageDraw.Draw(image)
    label(draw, (62, 46), "AFTERGLOW  /  PHYSICAL OUTPUT", 18, TEAL)
    label(draw, (58, 83), "Recovering the next DMX slot", 46)
    label(draw, (62, 151), "25 ms nominal grid   •   Injected monotonic clock   •   In-memory ArtDMX", 22, MUTED)

    draw.rounded_rectangle((60, 204, 1220, 515), 16, fill=SURFACE)
    draw.rectangle((point(50), 240, point(75), 490), fill="#20344b")
    for ms in [25, 50, 75, 100]:
        x = point(ms)
        draw.line((x, 246, x, 485), fill=GRID, width=1)
        label(draw, (x, 225), f"{ms} ms", 17, MUTED, "mt")

    for name, revision, row, log, accent in [
        ("Released scheduler", "4f65f06c", 353, RELEASED, AMBER),
        ("Local recovery", "Afterglow #122 on 4f65f06c", 452, CANDIDATE, TEAL),
    ]:
        label(draw, (85, row - 23), name, 24)
        label(draw, (85, row + 12), revision, 14, MUTED)
        draw.line((point(25), row, point(103), row), fill=GRID, width=2)
        sends = [item for item in log if item["event"] == "artdmx" and item["at-ms"] <= now]
        if now >= RELEASED_WAKE and log is RELEASED:
            x = point(GUARD_END)
            draw.line((x - 6, row - 6, x + 6, row + 6), fill=AMBER, width=2)
            draw.line((x + 6, row - 6, x - 6, row + 6), fill=AMBER, width=2)
            label(draw, (x, row - 19), "slot skipped", 17, AMBER, "ms")
        for item in sends:
            slot = int(item["at-ms"] // 25)
            marker(draw, item["at-ms"], row, item["rgb"], accent, item["frame-id"] == slot)

    if now >= GUARD_START:
        start, end = point(GUARD_START), point(min(now, GUARD_END))
        draw.line((start, 275, end, 275), fill=TEAL, width=3)
        draw.line((start, 270, start, 280), fill=TEAL, width=2)
        if now >= GUARD_END:
            draw.line((end, 270, end, 280), fill=TEAL, width=2)
        label(draw, ((point(GUARD_START) + point(GUARD_END)) / 2, 288), "12.5 ms minimum", 17, TEAL, "mt")

    if not still:
        cursor = point(max(25, now))
        draw.line((cursor, 241, cursor, 489), fill="#768aa0", width=1)
        label(draw, (1196, 190), f"{now:5.1f} ms", 18, MUTED, "rs")

    draw.rounded_rectangle((60, 543, 1220, 651), 16, outline=GRID, width=1)
    label(draw, (86, 561), step[0], 24, TEAL)
    label(draw, (86, 603), step[1], 19, WHITE)
    label(draw, (64, 675), "Filled dot = current frame     Open dot = held frame     R = first DMX channel", 14, MUTED)
    return image


steps = [
    ("Late first handoff", "Both schedulers enter the in-memory sink at 44 ms and receive success at 45 ms."),
    ("The spacing guard opens at 57.5 ms", "The next render completes at 47 ms, before its nominal 50 ms deadline."),
    ("Slot 2 recovered at 57.5 ms", "Local recovery sends frame 2. The released scheduler wakes at 75 ms."),
    ("Phase returns to the 25 ms grid", "Both wake at 75 ms. The released path still holds frame 1 after frame 2 expires."),
    ("Late render rejected at 76 ms", "The 100 ms slot still holds the last valid source in each trace."),
]
make_frame(103, steps[2], True).save(HERE / "next-slot-recovery.png")

command = ["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-f", "rawvideo", "-pix_fmt", "rgb24",
           "-s:v", f"{WIDTH}x{HEIGHT}", "-r", "20", "-i", "-", "-an", "-c:v", "libx264",
           "-threads", "2", "-pix_fmt", "yuv420p", "-movflags", "+faststart", str(HERE / "next-slot-replay.mp4")]
with subprocess.Popen(command, stdin=subprocess.PIPE) as encoder:
    moments = [(25, 45, 25), (45, 55, 28), (55, 63, 32), (63, 75, 26), (75, 103, 38), (103, 103, 22)]
    for index, (start, end, length) in enumerate(moments):
        for frame in range(length):
            now = start + ((end - start) * frame / (length - 1))
            if now < 45:
                step = steps[0]
            elif now < 57.5:
                step = steps[1]
            elif now < 75:
                step = steps[2]
            elif now < 76:
                step = steps[3]
            else:
                step = steps[4]
            encoder.stdin.write(make_frame(now, step).tobytes())
    encoder.stdin.close()
    if encoder.wait():
        raise SystemExit("ffmpeg could not encode the replay")
