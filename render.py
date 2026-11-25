import json
import subprocess
import sys
import tempfile
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path("/usr/share/fonts/truetype/dejavu")
TEXT = "#eff2ee"
MUTED = "#adbcb6"
TEAL = "#9ed4bf"
AMBER = "#efbe79"
STEPS = [
    ("Preferred ratios", "Ember starts at a one-beat period"),
    ("Turn one detent", "The encoder chooses the next preferred fraction"),
    ("Free ratios", "Set 5/11 through the shared show command"),
    ("Hold Accent, touch, and turn", "An exact fraction previews while you touch the encoder"),
    ("Release Accent first", "The preview stays active while you touch the encoder"),
    ("Lift your finger", "The owner and display restore 5/11"),
]


def font(size, bold=False, mono=False):
    family = "DejaVuSansMono" if mono else "DejaVuSans"
    return ImageFont.truetype(str(ROOT / (family + ("-Bold.ttf" if bold else ".ttf"))), size)


def frame(data, index):
    image = Image.new("RGB", (1280, 720), "#141a1b")
    draw = ImageDraw.Draw(image)
    title, detail = STEPS[index]
    draw.text((64, 48), "PUSH 3   /   EMBER", font=font(20, True), fill=TEAL)
    draw.text((63, 97), title, font=font(46, True), fill=TEXT)
    draw.text((65, 165), detail, font=font(23), fill=MUTED)

    for offset, (entry, title) in enumerate(zip(data["devices"], ("Poly aftertouch", "MPE"))):
        x = 64 + offset * 582
        row = entry["rows"][index]
        accent = AMBER if row["temporary?"] else TEAL
        draw.rounded_rectangle((x, 232, x + 570, 570), radius=17, fill="#212a2a", outline="#3b4c47")
        draw.text((x + 27, 254), title, font=font(23, True), fill=TEXT)
        draw.text((x + 27, 318), row["ratio"], font=font(70, True), fill=accent)
        draw.text((x + 29, 411), "Beat ratio", font=font(21), fill=MUTED)
        draw.line((x + 29, 478, x + 540, 478), fill="#41534e", width=1)
        draw.text((x + 29, 503), "Display " + row["display"], font=font(20, mono=True), fill=TEXT)
        state = "Temporary" if row["temporary?"] else "Committed"
        draw.text((x + 541, 505), state, font=font(20), fill=accent, anchor="rt")

    draw.text((64, 614), data["transport"], font=font(18), fill=MUTED)
    provenance = f"Tolglow {data['tolglow'][:8]}    Afterglow {data['afterglow'][:8]}"
    draw.text((64, 660), provenance, font=font(16, mono=True), fill="#889e95")
    return image


def render(directory):
    data = json.loads((directory / "capture.json").read_text())
    frame(data, len(STEPS) - 1).save(directory / "push3-ratio-restore.png")
    with tempfile.TemporaryDirectory() as staging:
        for index in range(len(STEPS)):
            frame(data, index).save(Path(staging) / f"{index:02d}.png")
        subprocess.run([
            "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-framerate", "1",
            "-i", str(Path(staging) / "%02d.png"), "-vf", "fps=24", "-c:v", "libx264",
            "-threads", "2", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
            str(directory / "push3-ratio-restore.mp4"),
        ], check=True)


if __name__ == "__main__":
    render(Path(sys.argv[1]))
