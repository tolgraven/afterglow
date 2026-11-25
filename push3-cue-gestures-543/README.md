# Push 3 cue-pad replay for #543

Afterglow `ffa824e7267ecf142d23c026036fe4a30aa07bf8` is based on `819b92c1572e2b683b99e93d8295cafd375e6386`. The clean local branch is `local/afterglow-push-cue-gesture-543`. It carries the shared cue-pad policy and the opt-in `:cue-gestures? true` Push 3 connection for User Mode or MPE. The target picker uses the existing pad ownership contract. The branch includes Afterglow #119 through its base.

All 27 Afterglow control, device, and codec namespaces passed on OpenJDK 21.0.13 with Clojure 1.12.7. The run executed 259 tests and 3,609 assertions. Definition spacing passed for the seven changed Clojure files. [Control tests](control-tests.log) · [Definition spacing](definition-spacing.log)

The owner replay pairs this Afterglow revision with Tolglow `77ea84f8598f5096585f5f47e4656d3ca98734f5`, the existing #516 cue-grid replay checkpoint. It opens the production connection via `tolglow.show/connect-device!`, manually advances the logical clock and owner, feeds synthetic bytes through an injected MIDI receiver, and uses an inert lighting sink. Both tests passed all 27 assertions. [Replay source](replay.clj) · [Replay log](replay.log)

- User Mode tap launched a persistent cue on beat 1. A release before the next grid boundary cancelled the queued hold by launch ID. A second hold was struck at 670 ms and fired on beat 2 at 1,000 ms. Note-off released only its instance. The configured modifier selected the active cue without issuing a command. A subsequent unmodified tap ended that exact instance.
- Two simultaneous MPE member voices edited separate running instances. Channel pressure and Glide addressed the first instance. CC74 Slide addressed component 2 of the second instance's position. Both remained running after note-off.

## Review media at `ffa824e7`

The 1280 × 800 still and 14.8-second GIF replay the test's recorded MIDI bytes, profile and owner steps, launch receipts, emitted values and instance states. The footer identifies the exact build pair. The animation presents User Mode followed by MPE at reading speed. Each test uses its own logical clock, and MIDI channel numbers are shown as 1–16. The capture records 37 steps and repeats the 27 passing assertions from the original replay. [Still](push3-gesture-replay-ffa824e7.png) · [GIF](push3-gesture-replay-ffa824e7.gif) · [Raw JSON](capture-ffa824e7.json) · [Capture log](capture-ffa824e7.log) · [Capture source](capture.clj) · [Media renderer](render-replay.py)

## Integration checks

Afterglow `1b89e08196ac0f0f9452e417221201cd0c46a348` merged #124 at `d1edde977b389404cde395d2742f7cc3046d3698`. All 282 control and engine tests passed with 3,771 assertions. The production owner replay passed all 27 assertions with the same Tolglow pin. All 37 recorded steps matched the original after normalizing random session command prefixes. [Control and engine tests](control-engine-tests-1b89e081.log) · [Replay log](capture-1b89e081.log) · [Raw JSON](capture-1b89e081.json)

Afterglow `008406520307fb7b1e3caa8763599ebefbcc6a5f` merged #125 at `e8f78be4bd8d8c4c22e982008949a50ebb5391a2`. The session merger preserves captured show identity for timed cues, held releases, encoder gestures, instance reorder, and #543's opt-in gestures. Admission uses the owner's current logical time. The focused Push 2, Push 3, session, policy, active-grid and codec lane passed 107 tests and 1,320 assertions. Definition spacing passed for all 259 tracked Clojure files. The owner replay again passed all 27 assertions and matched all 37 original steps after normalizing random session command prefixes. [Focused tests](push-session-tests-00840652.log) · [Definition spacing](definition-spacing-00840652.log) · [Replay log](capture-00840652.log) · [Raw JSON](capture-00840652.json)

The physical gate requires a timestamped input capture from a Push 3 with firmware, mode, and mapping or MPE zone recorded. Push 2 cue-pad policy integration and combined compound editor replay from #529 are separate gates.
