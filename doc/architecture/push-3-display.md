# Tethered Push 3 screen

Afterglow can send a 960 × 160 raster to a tethered Push 3 in controller mode. Tolglow supplies the same offscreen Studio views used on Push 2. MIDI User Mode and its captured layout select the controls. The display connects separately by USB bus and address. Live can own the screen even while User MIDI is available. Suspend the Tolglow session to release the screen before handing it back to Live. See [Ableton’s User Mode manual](https://www.ableton.com/en/push/manual/#user-mode) and [Push 3 MIDI FAQ](https://help.ableton.com/hc/en-us/articles/26201367296924-Push-3-MIDI-FAQ).

## Identify a device

Use a recent libusb 1.0, for example Debian’s `libusb-1.0-0` or Homebrew’s `libusb`. On macOS the default lookup also checks the Intel and Apple Silicon Homebrew prefixes. The REPL accepts an explicit `:library` path. Windows driver installation is described in [Ableton’s driver guide](https://help.ableton.com/hc/en-us/articles/10295607009436-Push-3-Display-Driver-Windows). This project’s ABI replay runs on 64-bit Linux and Apple Silicon macOS.

`libusb_init` scans every attached USB device. On one M4 Pro Mac with libusb 1.0.30 the scan stalled about 5 s on each of five unrelated hubs and drives, about 25 s in all (tolgraven/tolglow#704). libusb cannot skip that scan on macOS: `LIBUSB_OPTION_NO_DEVICE_DISCOVERY` and `libusb_wrap_sys_device` work only on Linux. Afterglow therefore creates one libusb context per library on first use and keeps it for the life of the process. Later `list`, `inspect` and display opens reuse it and pay only for opening, checking and claiming the device. A host can call `push-3.usb/prepare!` on a background thread at startup so that the first display open does not wait for the scan. `push-3.usb/release-contexts!` exits the shared contexts once every handle is closed. Each opened handle has a `:timing` map: whether the context was `:created` or `:reused`, its `libusb_init` time, and the open-and-claim time.

```sh
lein run -m afterglow.control.devices.push-3.qualification list
# Replace 2 and 7 with the bus and address reported for your tethered controller.
lein run -m afterglow.control.devices.push-3.qualification inspect 2 7
# Times the first scan, then list and two inspects in one process.
lein run -m afterglow.control.devices.push-3.qualification timing 2 7
```

These commands enumerate or read standard descriptors without claiming a display or sending frames. Save the second command’s EDN as the venue receipt. Tethered units must have USB VID:PID `2982:1969`, active configuration 1, and one alternate for interface 0. That interface must be named **Ableton Push 3 Display**, vendor class/subclass/protocol 255/255/255, and expose exactly two 512-byte bulk endpoints, OUT 0x01 and IN 0x81. On acquisition only interface 0 is claimed. Other functions on the composite device, including the xPort and audio interfaces, remain under their OS drivers. A busy display fails its acquisition. Replugging can change a unit’s bus address.

The 16-byte header and single 327,680-byte payload travel as two separate transfers to OUT 0x01. The 160 rows have 960 BGR565 little-endian visible pixels and 64 black padding pixels, then repeating line mask E7 F3 E7 FF. A per-session timer repeats the cached packed frame on a fixed grid of deadlines, 30 per second by default (`:refresh-hz`). Transfer time does not lower the rate. A frame that overruns its period skips the deadlines it missed instead of sending a burst. Before tolgraven/tolglow#704 the sink waited a fixed 33 ms after each frame. With payload transfers of about 11.7 ms that gave about 19.5 Hz. Updating the display content and repeating its last USB frame are independent. A failed or short transfer releases the interface and stops its timer. The USB call timeout is 400 ms per transfer. These fields and the continuous refresh follow a [physical tethered-device descriptor and frame trial](https://github.com/federico-pepe/push-tethered-app/blob/5bb4be81a30989a89084617e3180365dacf0be83/docs/archive/feasibility.md#83-the-frame-test), its [transfer notes](https://github.com/federico-pepe/push-tethered-app/blob/5bb4be81a30989a89084617e3180365dacf0be83/docs/protocol/display.md), and the [manufacturer’s earlier screen format](https://github.com/Ableton/push-interface/blob/5eb352fe3da9d07891efb7447191c03a66d9fbdd/doc/AbletonPush2MIDIDisplayInterface.asc).

## Frame completion

For controls that depend on the visible page, the image sink accepts
`:render-with-receipt!`. The receipt follows the complete header and payload
writes for that frame. A frame replaced in the packed buffer or interrupted
by an output failure earns no receipt. This is a USB transfer completion
receipt. Panel scanout still belongs to the device.

`push-3.display/refresh-receipt` reports, for an open or closed sink handle, the frames and bytes sent, the frames per second achieved between the first and last frame, the frame intervals and those longer than 1.5 periods, the header and payload transfer times (minimum, median, p95 and maximum), the sink open time and the libusb `:timing`. `show-chart` prints this receipt as EDN when it finishes.

## Physical qualification

1. Record controller model, firmware, OS, libusb version, connection mode and the read-only descriptor receipt. Confirm the selected unit’s MIDI and audio ports are visible.
2. Release the screen from its current owner. Explicitly run `lein run -m afterglow.control.devices.push-3.qualification show-chart 2 7 12`, substituting the scanned address. Photograph the top red, green, blue and white labels and the lower-right orientation mark. Inspect the outer one-pixel frame for cutoff, wrapping, swapped components or periodic idle-screen replacement.
3. Start a real browser-backed display. Select parameters, pages, simulator and rig, adjust the camera, and exercise a held MPE pad. Record the screen and the corresponding Studio capture. Verify audio and MIDI continue during screen refresh.
4. Suspend the device and return screen ownership to Live. Resume after Live releases the screen. Unplug while streaming, then enumerate again and use the new location. Record results and the errors observed. A standalone Push project or a firmware upgrade needs its own qualification.

## Hardware-free regression

`lein test afterglow.control.devices.push-3-display-test afterglow.control.devices.push-3-test` checks black padding, orientation, RGB primaries and session handoff. Linux and macOS compile a small recording libusb C library and exercise JNA calls, one shared context, short writes, busy claims, wrong interface names and cleanup. The recording descriptor reconstructs the display and xPort fields from the published observation. It is intentionally smaller than a real composite-device dump.

Given numbered native-size PNG captures from Studio, the following command sends each image through the production sink’s recording transport, decodes both transfers and checks every visible pixel against the source at 5/6/5 precision. It also replays a chart and measures 120 warm conversions. Physical screen ownership, colour fidelity and hardware timing still need the procedure above.

```sh
lein run -m afterglow.qa.push-3-display path/to/numbered-pngs /tmp/push3-replay
```
