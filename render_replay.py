import csv
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.animation import FFMpegWriter
import numpy as np

root = Path(__file__).resolve().parent
trace_a = (root / 'A-trace.csv').read_bytes()
trace_b = (root / 'B-trace.csv').read_bytes()
dmx_a = (root / 'A-dmx.bin').read_bytes()
dmx_b = (root / 'B-dmx.bin').read_bytes()
assert trace_a == trace_b and dmx_a == dmx_b
assert (root / 'A-native.bin').read_bytes() == (root / 'B-native.bin').read_bytes()
with (root / 'B-trace.csv').open() as source:
    rows = [{k: (v if k == 'event' else float(v)) for k, v in row.items()} for row in csv.DictReader(source)]
assert len(dmx_b) == 512 * len(rows)
frames = np.frombuffer(dmx_b, dtype=np.uint8).reshape(len(rows), 8, 8, 8).astype(float)
visible = [row for row in rows if row['beat'] <= 2.75]
beats = [row['beat'] for row in visible]

back = '#111923'
panel = '#192634'
white = '#f4f7fa'
label = '#a9b9c8'
blue = '#70ddcc'
gold = '#f7c577'
plt.rcParams.update({'font.family': 'DejaVu Sans', 'text.color': white, 'axes.labelcolor': label,
                     'xtick.color': label, 'ytick.color': label, 'axes.titlecolor': white})
fig = plt.figure(figsize=(12, 6.75), dpi=120, facecolor=back)
fig.text(.068, .917, 'Keyframe validation replay', size=26, weight='semibold')
fig.text(.068, .875, 'Released and candidate captures matched byte for byte across all 369 frames.', color=label, size=11)
level = fig.add_axes((.069, .522, .53, .259), facecolor=panel)
ratio = fig.add_axes((.069, .273, .53, .16), facecolor=panel, sharex=level)
fixtures = fig.add_axes((.662, .293, .27, .48), facecolor=panel)
for axis in (level, ratio, fixtures):
    for spine in axis.spines.values():
        spine.set_visible(False)
for axis in (level, ratio):
    axis.grid(alpha=.17)
    axis.set_xlim(0, 2.75)
    axis.tick_params(length=0)
    for x in [0.5, 1.125]:
        axis.axvline(x, color=label, alpha=.22, lw=1)
level.set(ylim=(0, 1), yticks=[0, .25, .5, .75, 1])
level.tick_params(labelbottom=False)
level.set_title('Native dimmer · first fixture', loc='left', pad=9, fontsize=12)
ratio.set(ylim=(.65, 5.35), yticks=[1, 2, 3, 4, 5], xticks=[0, .5, 1, 1.5, 2, 2.5])
ratio.set_title('Native beat ratio · first fixture', loc='left', pad=8, fontsize=12)
ratio.set_xlabel('Show beat', labelpad=8)
fixtures.set(xticks=[], yticks=[])
fixtures.set_title('64-fixture RGB preview', loc='left', pad=9, fontsize=12)
for axis, field, tint in [(level, 'dimmer', blue), (ratio, 'ratio', gold)]:
    axis.plot(beats, [row[field] for row in visible], drawstyle='steps-post' if field == 'ratio' else 'default',
              color=tint, alpha=.35, lw=1.8)
line_level, = level.plot([], [], color=blue, lw=2.5)
line_ratio, = ratio.plot([], [], color=gold, lw=2.5, drawstyle='steps-post')
point_level, = level.plot([], [], 'o', color=blue, ms=5)
point_ratio, = ratio.plot([], [], 'o', color=gold, ms=5)
image = fixtures.imshow(np.zeros((8, 8, 3)), vmin=0, vmax=1, interpolation='nearest')
readout = fig.text(.662, .244, '', color=label, size=10)
fig.text(.069, .138, '369 frames   ·   188,928 DMX bytes   ·   165,312 native field components',
         weight='semibold', size=12)
fig.text(.069, .085, '4f65f06c compared with the local backport of b247287d   ·   In-memory replay', color=label, size=9)


def update(i):
    row = visible[i]
    line_level.set_data(beats[:i+1], [r['dimmer'] for r in visible[:i+1]])
    line_ratio.set_data(beats[:i+1], [r['ratio'] for r in visible[:i+1]])
    point_level.set_data([row['beat']], [row['dimmer']])
    point_ratio.set_data([row['beat']], [row['ratio']])
    data = frames[i]
    dimmer = (data[:, :, 0:1] + data[:, :, 1:2] / 255) / 255
    image.set_data((dimmer * data[:, :, 2:5] / 255) ** .65)
    readout.set_text(f"Beat {row['beat']:.3f}  ·  Slot 1 {row['dmx_coarse']:.0f}  ·  Ratio {row['ratio']:.0f}")


update(68)
fig.savefig(root / 'keyframe-replay.png', facecolor=back)
writer = FFMpegWriter(fps=15, codec='libx264', extra_args=['-pix_fmt', 'yuv420p', '-threads', '2', '-movflags', '+faststart'])
with writer.saving(fig, str(root / 'keyframe-replay.mp4'), dpi=120):
    for index in range(len(visible)):
        update(index)
        writer.grab_frame(facecolor=back)
