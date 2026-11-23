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
frame. Instances below 0.75 ms keep their cadence. Twenty-four quiet frames
can restore one interval by a factor of two when its expected cost fits the
remaining budget. Smoothed duration and missed-frame frequency govern the two
windows. Epoch and definition changes reset their corresponding histories.
