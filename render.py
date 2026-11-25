"""Verify transferred pixels and compose the virtual Push replay evidence."""

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw, ImageFont, PngImagePlugin


LABELS = {
    "01-live": ("Hold Ember on the live grid", "The show owner launches a held cue from pad [7, 0].", 1.0),
    "02-open": ("Open full cue variations", "A pad press before the display transfer left the show unchanged.", 1.25),
    "03-saved": ("Append saved slot 1", "The show owner saves the running cue’s authored state.", 1.05),
    "04-applied": ("Apply a generated full state", "The show owner commits the generated parameters in one action.", 1.35),
    "05-rows": ("Browse parameter variations", "The same saved slot stays available in parameter rows.", 0.9),
    "06-recalled": ("Recall saved slot 1", "The show owner restores the original authored parameters.", 1.3),
    "07-released": ("Release Ember’s original pad", "The original held cue enters release, and the live screen returns.", 1.15),
}
FONT_DIRECTORY = Path("/usr/share/fonts/truetype/dejavu")
PNG_NOTE = "Virtual Push 3 User Mode replay with injected MIDI and USB transfers."


def decode(directory, frame):
    header = (directory / frame["header"]).read_bytes()
    payload = (directory / frame["payload"]).read_bytes()
    assert header == bytes.fromhex("ff cc aa 88 " + "00 " * 12)
    assert len(payload) == 327680
    wire = np.frombuffer(payload, dtype="<u2").reshape(160, 1024)
    mask = np.tile(np.array([0xF3E7, 0xFFE7], dtype=np.uint16), 512)
    bgr = wire ^ mask
    assert np.all(bgr[:, 960:] == 0)
    visible = bgr[:, :960]
    rgb565 = np.stack([visible & 31, (visible >> 5) & 63, visible >> 11], axis=-1).astype(np.uint8)
    with Image.open(directory / frame["source"]) as source:
        assert source.size == (960, 160)
        rgb = np.asarray(source.convert("RGB"))
    assert np.array_equal(rgb565, rgb >> np.array([3, 2, 3], dtype=np.uint8)), frame["label"]
    pixels = (rgb565 << np.array([3, 2, 3], dtype=np.uint8)) | (rgb565 >> np.array([2, 4, 2], dtype=np.uint8))
    image = Image.fromarray(pixels)
    filename = f"frames/{frame['label']}-transferred.png"
    meta = PngImagePlugin.PngInfo()
    meta.add_text("Source", PNG_NOTE)
    image.save(directory / filename, pnginfo=meta)
    frame.update(decoded=filename, payload_sha256=hashlib.sha256(payload).hexdigest(),
                 visible_pixels_verified=960 * 160)
    return image


def font(size, bold=False, mono=False):
    name = "DejaVuSansMono" if mono else "DejaVuSans"
    return ImageFont.truetype(str(FONT_DIRECTORY / f"{name}{'-Bold' if bold else ''}.ttf"), size)


def compose(image, frame):
    title, detail, _ = LABELS[frame["label"]]
    canvas = Image.new("RGB", (1280, 520), "#101519")
    draw = ImageDraw.Draw(canvas)
    primary = "#edf2ed"
    secondary = "#b6c4c5"
    accent = "#80d6ce"

    draw.text((160, 43), "Tolglow on Push 3", font=font(30, bold=True), fill=primary)
    tag = "VIRTUAL · INJECTED MIDI + USB"
    tag_width = draw.textlength(tag, font=font(15, mono=True))
    draw.rounded_rectangle((1118 - tag_width - 32, 43, 1120, 73), radius=6, fill="#173337")
    draw.text((1102 - tag_width, 50), tag, font=font(15, mono=True), fill=accent)
    draw.text((160, 106), "TRANSFERRED PUSH DISPLAY  ·  960 × 160", font=font(15, mono=True), fill=secondary)

    draw.rounded_rectangle((151, 135, 1129, 314), radius=10, fill="#283237")
    canvas.paste(image, (160, 144))

    draw.text((160, 337), title, font=font(31, bold=True), fill=primary)
    draw.text((160, 383), detail, font=font(17), fill=secondary)

    state = frame["params"]
    fields = [f"LEVEL   {state['level']:.2f}", f"BEAT RATIO   {state['period']}",
              f"PREVIEW DIMMER   {frame['dimmer-byte']}", f"PHASE   {frame['phase'].upper()}"]
    draw.line((160, 442, 1120, 442), fill="#334247", width=1)
    for x, field in zip([160, 377, 625, 928], fields, strict=True):
        draw.text((x, 464), field, font=font(17, mono=True), fill=accent)
    return canvas


def video(directory, screens):
    path = directory / "push-3-variation-overlay.mp4"
    duration = sum(LABELS[label][2] for label, _ in screens)
    with tempfile.TemporaryDirectory(prefix="push3-replay-video-") as output:
        stages = Path(output)
        sequence = ["ffconcat version 1.0"]
        for label, screen in screens:
            image_path = stages / f"{label}.png"
            screen.save(image_path)
            sequence.extend([f"file {image_path}", f"duration {LABELS[label][2]}"])
        sequence.append(f"file {image_path}")
        timeline = stages / "replay.ffconcat"
        timeline.write_text("\n".join(sequence) + "\n")
        subprocess.run(["ffmpeg", "-v", "error", "-y", "-f", "concat", "-safe", "0", "-i", str(timeline),
                        "-vf", "fps=24,format=yuv420p", "-c:v", "libx264", "-threads", "1", "-crf", "16",
                        "-t", str(duration),
                        "-movflags", "+faststart", "-metadata", "comment=" + PNG_NOTE, str(path)], check=True)
    probe = subprocess.check_output(["ffprobe", "-v", "error", "-show_entries",
                                     "stream=codec_name,width,height:format=duration", "-of", "json", str(path)])
    details = json.loads(probe)
    assert details["streams"] == [{"codec_name": "h264", "width": 1280, "height": 520}]
    assert abs(float(details["format"]["duration"]) - duration) <= 1 / 24
    return details


def main(directory):
    receipt_path = directory / "receipts.json"
    receipt = json.loads(receipt_path.read_text())
    frames = receipt["frames"]
    assert receipt["injected"] is True
    assert [frame["label"] for frame in frames] == list(LABELS)
    assert [frame["ack"]["status"] for frame in frames if frame["ack"]] == ["accepted"] * 5
    assert receipt["blocked-before-transfer"]["unchanged-params"]
    assert receipt["blocked-before-transfer"]["unchanged-receipt"] == frames[0]["ack"]["command-id"]
    assert frames[0]["params"] == frames[2]["params"] == frames[5]["params"]
    assert frames[3]["params"] != frames[0]["params"]
    assert frames[-1]["phase"] == "releasing"

    screens = [(frame["label"], compose(decode(directory, frame), frame)) for frame in frames]
    info = PngImagePlugin.PngInfo()
    info.add_text("Source", PNG_NOTE)
    screens[2][1].save(directory / "push-3-variation-overlay.png", pnginfo=info)
    receipt["video"] = video(directory, screens)
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"{len(frames)} native frames matched every Chromium pixel at BGR565 precision")
    print("The five owner receipts are accepted")
    print(receipt["video"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    main(parser.parse_args().directory.resolve())
