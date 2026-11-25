import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from PIL import Image


directory = Path(__file__).resolve().parent
before = json.loads((directory / "before.json").read_text())
after = json.loads((directory / "after.json").read_text())

levels = [100, 75, 50, 25, 10, 0]
comparisons = (
    (before, "Released renderer", "#b84335", "--"),
    (after, "Corrected renderer", "#147356", "-"),
)
cues = (("off", "Cue authored off"), ("full", "Cue authored full"))


def read_samples(capture, cue):
    runs = [run for run in capture["runs"] if run["cue"] == cue]
    assert {(run["batch"], run["native"]) for run in runs} == {
        (False, False), (False, True), (True, False), (True, True),
    }
    assert all(run["samples"] == runs[0]["samples"] for run in runs)
    assert [round(point["level"] * 100) for point in runs[0]["samples"]] == levels
    return [point["dmx"] for point in runs[0]["samples"]]


samples = {(capture["afterglow"], cue): read_samples(capture, cue)
           for capture, _, _, _ in comparisons for cue, _ in cues}
assert before["tolglow"] == after["tolglow"]
assert before["range"] == after["range"] == [255, 0]
pins = (
    f"Tolglow   {before['tolglow']}",
    f"Afterglow released   {before['afterglow']}",
    f"Afterglow corrected  {after['afterglow']}",
)


def draw(step):
    fig, axes = plt.subplots(1, 2, figsize=(10.8, 5.2), dpi=104, sharey=True)
    fig.patch.set_facecolor("#f7f7f2")
    fig.subplots_adjust(top=0.705, bottom=0.32, left=0.095, right=0.961, wspace=0.18)
    fig.text(0.095, 0.916, "Profiled fog group fader", fontsize=22, weight="bold", color="#142820")
    fig.text(0.095, 0.839, "In-memory DMX capture  ·  Reversed range, 255 off and 0 full",
             fontsize=10, color="#42554c")
    fig.text(0.957, 0.914, f"{levels[step]}%", ha="right", fontsize=23, weight="bold", color="#147356")
    fig.text(0.957, 0.841, "Group level", ha="right", fontsize=10, color="#42554c")

    for ax, (cue, title) in zip(axes, cues):
        ax.set_facecolor("#ffffff")
        ax.set_title(title, loc="left", fontsize=12, weight="bold", color="#142820", pad=8)
        ax.set_xlim(104, -4)
        ax.set_ylim(-6, 106)
        ax.set_xticks([100, 75, 50, 25, 0])
        ax.set_yticks([0, 25, 50, 75, 100])
        ax.grid(axis="y", linewidth=0.7, color="#dce2dc")
        ax.set_axisbelow(True)
        ax.axvline(levels[step], color="#bcc6bd", linewidth=1.15, zorder=1)
        for spine in ("top", "right"):
            ax.spines[spine].set_visible(False)
        for spine in ("left", "bottom"):
            ax.spines[spine].set_color("#a8b5aa")
        ax.tick_params(colors="#42554c", length=3)
        ax.set_xlabel("Group level (%)", color="#42554c")

        for index, (capture, label, color, line_style) in enumerate(comparisons):
            counts = samples[capture["afterglow"], cue]
            off, full = capture["range"]
            flow = [100 * (value - off) / (full - off) for value in counts]
            ax.plot(levels[:step + 1], flow[:step + 1], color=color, linestyle=line_style, linewidth=2.2,
                    marker="o", markersize=4.7, zorder=2 + index)
            ax.scatter(levels[step], flow[step], color=color, edgecolor="white", linewidth=1, s=43,
                       zorder=4 + index)
            ax.text(0.46 * index, -0.35, f"{label}\nDMX byte {counts[step]}",
                    transform=ax.transAxes, color=color, fontsize=9, weight="bold", va="top")

    axes[0].set_ylabel("Estimated rated flow (%)", color="#42554c")
    for index, pin in enumerate(pins):
        fig.text(0.095, 0.10 - index * 0.031, pin, fontsize=7.3, color="#42554c", family="monospace")
    fig.canvas.draw()
    width, height = fig.canvas.get_width_height()
    image = Image.frombytes("RGBA", (width, height), bytes(fig.canvas.buffer_rgba())).convert("RGB")
    plt.close(fig)
    return image


images = [draw(step) for step in range(len(levels))]
comment = ("In-memory DMX replay. Exact capture revisions.\n" + "\n".join(pins)).encode()
images[0].save(directory / "profiled-fog-fader.gif", save_all=True, append_images=images[1:],
               duration=[1100, 850, 850, 850, 850, 1500], loop=0, disposal=2, comment=comment)
