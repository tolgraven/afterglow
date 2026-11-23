# Venue fog from delivered DMX

`afterglow.render.atmosphere` estimates aerosol from a fogger’s rated output. Specify the volume of fog the manufacturer rates at full output, in cubic metres per minute. Fluid consumption in mL/min is a different quantity. The model tracks equivalent rated fog volume, which can exceed the room volume after sustained output. It cannot establish safe exposure, absolute particle concentration or measured visibility.

```clojure
{:id :jet :position [0 0.4 -3] :universe 1 :address 240 :channels {:fog 1}
 :fogger {:flow-m3-min 80 :dmx-range [15 220] :mixing-seconds 8 :direction [0 0.2 1]}}
```

The optional physical DMX endpoints set off and full flow; insert the equipment’s real activation threshold. The curve between those points is linear. A fixture can span coarse and fine slots in different universes. The nozzle direction is in world coordinates. A successful packet changes the pump level for the following interval. Integrate the previous level first. A missing universe retains its last delivered value.

Use room width, height and depth in metres, optional `:air-changes-per-hour` (default 0) and `:fog-half-life-s` (default 180). The model separates each nozzle’s concentrated plume from the mixed room. Local fog mixes exponentially at a rate of 1/`:mixing-seconds` per second. Ventilation and deposition remove mass from both components. The solution integrates held flows analytically, so increasing the display or DMX frame rate does not increase the amount emitted.

Call `plan` with the room and compiled fixture patch, then `initial` with the show epoch and monotonic time in ms. Pass accepted universe buffers and their send time to `present`, or call `advance` to project to a later time. Preserve the returned value as the state of this venue. On restore `reconfigure` rebases persisted quantities at the new clock origin and releases pump levels. A renderer can reconstruct local plumes and room haze from `:local-m3`, `:emitted-m3` and `:mixed-density` without replaying every frame.

## Stationary sightline calibration

A locked camera observes a steady bright target and adjacent dark reference through the same air. Record their linear luma, in a clear room, through a burst, and through its clearing tail. Afterglow derives transmission from the patch contrast divided by the clear contrast. The negative logarithm gives optical depth along the measured path. A metered nozzle supplies the independent input needed to fit plume mixing time and optical extinction per unit of rated fog. A manually operated, unmetered burst can supply the effective room clearance half-life alone. Moving the camera, changing the target light or aiming into the nozzle can invalidate the fit.

Call `afterglow.render.atmosphere.calibration/fit` with ordered `:samples` containing elapsed milliseconds, `:bright`, `:dark` and `:phase` (baseline, active or clearing), held `:flows` as timestamped `:flow-m3-s`, room `:volume-m3` and sightline `:path-m`. The full fit accounts for both retained plume and mixed room fog. Fitting belongs outside the live renderer.

Store the accepted `:clearance-half-life-s`, `:extinction-per-m` and `:reference-path-m` under the room’s `:measured-fog` map and any fitted `:mixing-seconds` on the measured nozzle. The effective clearance already includes deposition and air exchange under the scanned conditions. The published mixed-room `:fog-level` is the fraction of contrast lost at that sightline, from 0 to 1. The last successfully presented fog address supplies `:last-presented-ms`, which remains fixed if observation time advances through missed packets.

## How much of a delivered plume will still reach the room?

Call `(coasting-peak plan state)` to estimate the greatest room-wide attenuation if all pumps stop at this sample. It returns `:fog-level`, the mixed volume in `:mixed-m3` and the time to the peak in `:after-s`. A controller can use that forecast to avoid repeatedly pulsing a machine while a slow jet is still localized.

For initial mixed volume `M`, local plume volumes `Lᵢ`, mixing rates `kᵢ` and the venue clearance rate `d`, the mixed volume after stopping is `exp(−d t) × [M + Σ Lᵢ (1 − exp(−kᵢ t))]`. The derivative has at most one positive root. The implementation brackets that root and solves for it, using the current time as the peak when the room is already clearing. The sightline calculation uses the same room volume and calibrated coefficients as `advance`.

## Calibrated sightlines

The effect library's `:optics/fog-transmission` material takes the same extinction per metre and relative fog density as the room model, plus the ray's length in metres. Transmitted direct light is `exp(-extinction × density × distance)`. At unit-density extinction 1.25 per metre, a 10% uniform mixture transmits about 36.8% across eight metres. Negative material inputs are clamped to zero, so a zero-length path or empty room transmits all the light.

The host evaluates the material's optical-depth expression once per mixed-state update. It computes the absorbed fraction with `expm1` so a controller can still observe trace haze. Studio consumes a static ES module emitted from the same material for the GPU volume pass and reflected-light paths. From the paired Tolglow checkout, regenerate it with `lein run -m afterglow.render.fog-optics js/preview/fog-optics.generated.js` after changing this material.
