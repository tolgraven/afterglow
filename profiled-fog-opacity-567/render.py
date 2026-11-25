import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


directory = Path(__file__).resolve().parent
before = json.loads((directory / "before.json").read_text())
after = json.loads((directory / "after.json").read_text())

def samples(capture, cue):
    runs = [run for run in capture["runs"] if run["cue"] == cue]
    assert {(run["batch"], run["native"]) for run in runs} == {
        (False, False), (False, True), (True, False), (True, True),
    }
    assert all(run["samples"] == runs[0]["samples"] for run in runs)
    return runs[0]["samples"]

fig, axes = plt.subplots(1, 2, figsize=(10.4, 4.5), sharey=True)
fig.patch.set_facecolor("#f7f7f2")
fig.subplots_adjust(top=0.72, bottom=0.24, left=0.105, right=0.96, wspace=0.17)
fig.text(0.105, 0.93, "Profiled fog group fader", fontsize=21, weight="bold", color="#142820")
fig.text(0.105, 0.845, "Captured Tolglow DMX on a reversed-range nozzle  ·  255 off, 0 full",
         fontsize=10.5, color="#42554c")
for ax, cue, title in zip(axes, ("off", "full"), ("Cue authored off", "Cue authored full")):
    for capture, label, color, line_style in (
        (before, "Released renderer", "#be4937", "--"),
        (after, "Corrected renderer", "#147356", "-"),
    ):
        points = samples(capture, cue)
        levels = [100 * point["level"] for point in points]
        off, full = capture["range"]
        flows = [100 * (point["dmx"] - off) / (full - off) for point in points]
        ax.plot(levels, flows, label=label, color=color, linestyle=line_style, linewidth=2,
                marker="o", markersize=4.6, clip_on=False)
    ax.set_facecolor("#ffffff")
    ax.set_title(title, loc="left", fontsize=12, weight="bold", color="#142820", pad=9)
    ax.set_xlim(103, -3)
    ax.set_ylim(-5, 105)
    ax.set_xticks([100, 75, 50, 25, 0])
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_xlabel("Group level (%)", color="#42554c")
    ax.grid(axis="y", linewidth=0.7, color="#dce2dc")
    ax.set_axisbelow(True)
    ax.tick_params(colors="#42554c", length=3)
    for spine in ("top", "right"):
        ax.spines[spine].set_visible(False)
    for spine in ("left", "bottom"):
        ax.spines[spine].set_color("#a8b5aa")
axes[0].set_ylabel("Fog flow from captured bytes (%)", color="#42554c")
handles, labels = axes[0].get_legend_handles_labels()
fig.legend(handles, labels, loc="lower left", bbox_to_anchor=(0.095, 0.083), ncols=2,
           frameon=False, labelcolor="#142820", handlelength=2.7)
fig.text(0.105, 0.056, "Ordinary and native effects matched in both show modes. In-memory frames.",
         color="#42554c", fontsize=8.3)
fig.savefig(directory / "profiled-fog-fader.png", dpi=160, facecolor=fig.get_facecolor())
