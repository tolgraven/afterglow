import csv
from pathlib import Path
import subprocess

import matplotlib

matplotlib.use("Agg")
from matplotlib import pyplot as plt
from matplotlib.colors import to_rgb
from matplotlib.patches import Circle, FancyBboxPatch


ROOT = Path(__file__).resolve().parent
with (ROOT / "trace.csv").open() as capture:
    rows = [
        {key: value if key in {"event", "settled"} else float(value) for key, value in row.items()}
        for row in csv.DictReader(capture)
    ]
head, base, feature = (ROOT / "pins.txt").read_text().splitlines()
settled = next(row for row in rows if row["event"] == "settled")
timeline = [row for row in rows if row["beat"] <= 2.75]
last = rows[-1]

background = "#101822"
panel_fill = "#172333"
grid = "#28384a"
ink = "#f1f5fb"
soft = "#aabbd1"
teal = "#65dfc7"
gold = "#ffd184"
target = "#b999d9"

fig = plt.figure(figsize=(12.8, 7.2), dpi=110, facecolor=background)
fig.text(0.066, 0.936, "Reactive effect retargeting", color=ink, fontsize=28, weight="semibold")
fig.text(0.067, 0.894, "Captured from the Afterglow runtime and renderer. Output stayed in memory.",
         color=soft, fontsize=11)

level = fig.add_axes((0.068, 0.506, 0.59, 0.283), facecolor=background)
ratio = fig.add_axes((0.068, 0.285, 0.59, 0.142), facecolor=background, sharex=level)

for ax in (level, ratio):
    ax.set_axisbelow(True)
    ax.grid(axis="y", color=grid, linewidth=0.8)
    ax.tick_params(colors=soft, labelsize=9, length=0, pad=8)
    for spine in ax.spines.values():
        spine.set_visible(False)
    for event in [row for row in timeline if row["event"] in {"change", "retarget", "settled"}]:
        ax.axvline(event["beat"], color=grid, linewidth=1.15)
    ax.axvspan(settled["beat"], timeline[-1]["beat"], color=teal, alpha=0.07, linewidth=0)

level.set(ylim=(0, 1.0), yticks=[0, 0.25, 0.5, 0.75, 1.0], xlim=(0, timeline[-1]["beat"]))
level.tick_params(labelbottom=False)
level.set_title("Resolved dimmer", loc="left", color=ink, fontsize=12, pad=14, weight="semibold")
ratio.set(ylim=(0.75, 5.25), yticks=[1, 3, 5], xticks=[0, 0.5, 1, 1.5, 2, 2.5])
ratio.set_title("Native beat ratio", loc="left", color=ink, fontsize=12, pad=12, weight="semibold")
ratio.set_xlabel("Show beat", color=soft, fontsize=9, labelpad=6)

event_labels = {"change": "Inputs change", "retarget": "Retarget", "settled": "Settled"}
for event in [row for row in timeline if row["event"] in event_labels]:
    level.text(event["beat"], 0.968, event_labels[event["event"]], va="top", ha="left",
               color=soft, fontsize=9, backgroundcolor=background)

beats = [row["beat"] for row in timeline]
for ax, field, desired, color in (
    (level, "preview_level", "target_level", teal),
    (ratio, "native_ratio", "target_ratio", gold),
):
    style = "steps-post" if ax is ratio else "default"
    ax.plot(beats, [row[field] for row in timeline], color=color, linewidth=2.2, alpha=0.21, drawstyle=style)
    ax.plot(beats, [row[desired] for row in timeline], color=target, linewidth=1.2, alpha=0.72,
            linestyle=(0, (3, 4)), drawstyle="steps-post")

level_line, = level.plot([], [], color=teal, linewidth=2.5, solid_capstyle="round")
ratio_line, = ratio.plot([], [], color=gold, linewidth=2.5, drawstyle="steps-post", solid_capstyle="round")
level_point, = level.plot([], [], "o", color=teal, markersize=6, markeredgecolor=background)
ratio_point, = ratio.plot([], [], "o", color=gold, markersize=6, markeredgecolor=background)

fig.text(0.072, 0.216, "Captured output", color=teal, fontsize=9, weight="medium")
fig.text(0.172, 0.216, "Target", color=target, fontsize=9, weight="medium")

card = fig.add_axes((0.70, 0.267, 0.239, 0.567))
card.set_axis_off()
card.add_patch(FancyBboxPatch((0.0, 0.0), 1.0, 1.0, boxstyle="round,pad=0.0,rounding_size=0.03",
                             transform=card.transAxes, facecolor=panel_fill, edgecolor=grid, linewidth=1.1))
card.text(0.10, 0.91, "Fixture preview", color=ink, fontsize=13, weight="semibold", transform=card.transAxes)
card.text(0.10, 0.849, "Illustration from resolved dimmer", color=soft, fontsize=8.5, transform=card.transAxes)

lamp = fig.add_axes((0.752, 0.52, 0.135, 0.221), aspect="equal")
lamp.set_axis_off()
lamp_rim = Circle((0.5, 0.5), 0.34, color="#24394b", linewidth=0)
lamp_center = Circle((0.5, 0.5), 0.24, color=teal, linewidth=0)
lamp.add_patch(lamp_rim)
lamp.add_patch(lamp_center)

phase = card.text(0.10, 0.435, "", color=teal, fontsize=10, weight="semibold", transform=card.transAxes)
values = card.text(0.10, 0.365, "", color=ink, fontsize=12, transform=card.transAxes)
frame_label = card.text(0.10, 0.262, "", color=soft, fontsize=8.5, transform=card.transAxes)
input_label = card.text(0.10, 0.191, "", color=soft, fontsize=8.5, transform=card.transAxes)
counts = card.text(0.10, 0.085, "", color=ink, fontsize=10, weight="medium", transform=card.transAxes)

hold_frames = int(last["frame"] - settled["frame"])
hold_seconds = (last["time_ms"] - settled["time_ms"]) / 1000
added_calls = int(last["calculations"] - settled["calculations"])
fig.text(0.068, 0.144, f"{hold_frames} settled frames · {added_calls} extra calculations · {hold_seconds:.1f} s of show time",
         color=ink, fontsize=14, weight="semibold")
fig.text(0.068, 0.094, f"Candidate  {head}     Released base  {base}",
         color=soft, fontsize=7.5, family="monospace")
fig.text(0.068, 0.067, f"Source     {feature}     Output trace   369 captures · Universe 1 · Slot 1",
         color=soft, fontsize=7.5, family="monospace")


def mix(left, right, fraction):
    return tuple(a + (b - a) * fraction for a, b in zip(to_rgb(left), to_rgb(right)))


def update(row):
    displayed_beat = min(row["beat"], timeline[-1]["beat"])
    visible = [sample for sample in timeline if sample["beat"] <= displayed_beat]
    level_line.set_data([sample["beat"] for sample in visible], [sample["preview_level"] for sample in visible])
    ratio_line.set_data([sample["beat"] for sample in visible], [sample["native_ratio"] for sample in visible])
    level_point.set_data([displayed_beat], [row["preview_level"]])
    ratio_point.set_data([displayed_beat], [row["native_ratio"]])

    brightness = row["preview_level"]
    lamp_rim.set_color(mix("#24394b", "#459f96", brightness))
    lamp_center.set_color(mix("#364963", "#ecffed", brightness))
    phase.set_text({"initial": "Initial sample", "change": "Transition started", "retarget": "Transition retargeted"}
                   .get(row["event"], "Settled hold" if row["settled"] == "true" else "Transitioning"))
    values.set_text(f"{row['preview_level']:.3f}  ·  DMX {row['dmx_slot_1']:03.0f}")
    frame_label.set_text(f"Frame {row['frame'] + 1:.0f} of {len(rows)}  ·  Beat {row['beat']:.3f}")
    input_label.set_text(f"Ratom {row['level']:.2f}  ·  Subscription bias {row['bias']:.2f}")
    counts.set_text(f"{row['calculations']:.0f} effect calculations so far")
    fig.canvas.draw()


update(last)
fig.savefig(ROOT / "reactive-effect-still.png", dpi=fig.dpi, facecolor=background)

width, height = fig.canvas.get_width_height()
indices = [0] * 6 + list(range(0, 89, 2)) + list(range(108, len(rows), 26)) + [len(rows) - 1] * 17
with subprocess.Popen(
    ["ffmpeg", "-y", "-loglevel", "error", "-f", "rawvideo", "-pixel_format", "rgba",
     "-video_size", f"{width}x{height}", "-framerate", "12", "-i", "-", "-an",
     "-c:v", "libx264", "-crf", "19", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
     "-metadata", f"title=Afterglow reactive effect capture {head}", str(ROOT / "reactive-effect-retarget.mp4")],
    stdin=subprocess.PIPE,
) as encoder:
    for index in indices:
        update(rows[index])
        encoder.stdin.write(fig.canvas.buffer_rgba())
    encoder.stdin.close()
    if encoder.wait():
        raise RuntimeError("FFmpeg could not encode the retarget capture")
