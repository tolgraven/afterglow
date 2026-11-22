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
