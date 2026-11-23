# Adaptive effect evaluation

A show host can give predictive effects more time between expensive samples
when the actual frame duration leaves too little headroom. Each show owns its
own policy state. The engine still owns interpolation, future sampling and
validation of eligible effects.

Create one `afterglow.runtime.cadence/observer` per measured frame. Pass its
`:measure-effect` function to the engine. The function records elapsed time
on the actual worker thread around a real evaluation and returns its result.
Several evaluations of the same instance can run in the same frame. The observer
counts every call. An evaluation that throws still records its elapsed time
before the engine handles the fault.

After the frame, pass the observer's samples, the frame duration, output
period, epoch and active instance versions to `cadence/advance`. It returns
the disposable state and a `:keyframe-intervals` map for the next frame. Pass
the map with the next frame's inputs. `cadence/ranked-costs` returns the measured
cost per real evaluation, cumulative evaluations, frames containing samples,
eligibility and current stride. Wall-clock measurements stay outside show
definitions and portable model state.

Defaults reserve 15% of the output period. Three consecutive frames of
sustained pressure can double one predictive instance's interval, up to eight
frames. The policy first considers the highest estimated cost per scheduled
frame. Two consecutive real samples must meet the cost floor before an
instance can slow down. Two consecutive samples below the floor (0.75 ms
by default) restore that instance to its authored cadence even in a busy
scene. Interpolated frames do not count as samples. Twenty-four quiet frames
can restore one interval by a factor of two when its expected cost fits the
remaining budget. Smoothed duration and missed-frame frequency govern the two
windows. Epoch and definition changes reset their corresponding histories.

A physical host can include the nominal deadline index in `:output-slot`.
At 40 Hz, rendering slots 20, 25 and 31 means the last two renders advanced
the show by 11 slots (275 ms). A 50 ms forecast would already have expired
by the next render. Reopening it can cost two effect calls, one at the
current time and one in the future. The policy therefore asks for an
automatic interval long enough to cover the last two observed gaps. An
effect whose musical ceiling or global limit is shorter keeps its ordinary
sampling. Direct, discrete cues and authored tween intervals keep their
existing behavior. The two-gap window advances on each completed render,
so a single long gap drops out after two subsequent gaps. During startup,
after a clock restart and for unscheduled renders the minimum is two slots.

A host may set `:defer-live-slowdown?` on the frame timing input while it is
reducing the keyframe rate of mounted presentation surfaces. Measurements and
recovery continue through this interval. Once the visual sampler reaches its
lowest rate, the host clears the flag and normal cost-ranked effect throttling
resumes if pressure persists.

## Giving a particular effect less time between samples

Put `:keyframes {:max-interval {:beats 1/8}}` on a continuous moving or color
effect to limit how far ahead overload protection can sample it. With only a
maximum configured, ordinary playback still evaluates the effect every frame.
At 40 Hz, one eighth of a beat permits two frames at 120 BPM and one frame at
240 BPM. The other effects in a compound cue have independent limits.

A positive duration may use beats, bars, phrases or milliseconds. Bars and phrases
use the current meter. An explicit `:interval` remains the authored cadence.
For example, `{:interval {:beats 1} :max-interval {:beats 1/2}}` retains the
one-beat tween and gives the governor no additional slowdown on that effect.
On a tempo or meter edit, automatic windows take a fresh sample at the live
clock. An authored tween keeps its last presented value for continuity.

Hosts can use `cadence/maximum-stride` with the effect's keyframe declaration,
transport, output period and global maximum. Send the resulting per-instance
limits in `:max-strides` to `cadence/advance`. Apply a changed ceiling to the
current frame's requested intervals before passing them to workers, including on
the frame that accepts a tempo or meter command. The governor skips an effect
already at its ceiling when choosing the next expensive effect, and spends the
same pressure decision on an eligible sibling. The diagnostic ranking reports
both `:stride` and its effective `:max-stride`.
