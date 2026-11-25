# Publication deadline recovery for Tolglow #387

Afterglow master `4f65f06ccdf6b75418aa9a66deb6e4cb894d1937` still rounds the half-period spacing guard up to a nominal deadline for every handoff. Draft [Afterglow #122](https://github.com/tolgraven/afterglow/pull/122) is open at `28616f127bf47afae1c98010ce5d154bbb5b3710`. The local forward-port `c8750427ac5e046ef5ab121a52008a4336c2da77` keeps the draft's scheduler logic on released master, including master’s later wire-patch bookkeeping.

The local scheduler wakes at the later of the next nominal deadline and the previous successful handoff’s return plus half a period. Under the publication lock it resamples the clock and selects the current slot. A wake before the guard requeues. A wake after the slot ends uses the then-current slot once. A failed handoff or expired packing attempt still recovers on a future grid deadline. If a successful handoff has already crossed a nominal deadline when it returns, that slot stays skipped and the spacing guard can delay the next future slot. The scheduler checks expiry after final buffer preparation and admits direct-mode samples against their original deadline.

## Captured 25 ms trace

| Scenario | Released scheduler | Local forward-port |
| --- | --- | --- |
| Handoff enters at 44 ms and returns at 45 ms | Wakes at 75 ms, expires ready frame 2 and holds frame 1 | Rejects an early callback at 50 ms, sends frame 2 at 57.5 ms and returns to the nominal grid at 75 ms |
| The callback resumes at the 75 ms boundary | One send for slot 3 using frame 3 | One send for slot 3 using frame 3 |
| First sink attempt throws at 49.9 ms | Grid recovery at 75 ms with idle bytes | Grid recovery at 75 ms with idle bytes |
| Packing reaches the 50 ms boundary | Skips the expired send and recovers at 75 ms | Skips the expired send and recovers at 75 ms |
| Frame 3 completes at 76 ms for its 75 ms deadline | Drops it and holds frame 1 at 100 ms | Drops it and holds frame 2 at 100 ms |

The recovered handoff left 12.5 ms after the preceding successful return. The first and second sink entries were 13.5 ms apart. Frame 2 completed at 47 ms. Its red byte was 180 and the held frame 1 red byte was 90. All emitted datagrams in the deterministic harness passed checks for the 530-byte packet length and ArtDMX address and payload-size bytes. The test subset executed scheduler and timeline tests and the Art-Net packet tests. It excluded the UDP loopback test. Baseline ran 32 tests with 214 assertions and candidate ran 33 with 222. Both passed. The released expiration counter can also increment when a previously published source ages out of history after a newer source takes over. In the recovery trace it increments at 75 ms for frame 1, which already reached the sink at 44 ms. The slot comparison uses captured handoff times, source IDs and ArtDMX bytes.

## Recorded performance

The earlier M4 Air exact-draft comparison used an in-memory ArtDMX sink. It delivered 1,200/1,200 slots against 1,197/1,200 on the original wake policy. Its shortest candidate gap was 14.61 ms. It delivered 314 current sources and held 886, while the controls delivered 323 current and held 874. All packets were complete and every render exceeded 25 ms. The combined #121/#122 capture also delivered 1,200/1,200 versus 1,192/1,200 on the controls with 369 current and 831 held. These measurements cover sink cadence on the earlier revisions. Current-base verification uses injected time and in-memory bytes. Hardware gateway delivery and sustained fresh 40 Hz rendering remain unmeasured in this lane. [Exact M4 receipt](https://github.com/tolgraven/tolglow/tree/e68b8783ca589a86333c98106dcd17c65b07eb09/cadence/weighted-publication-spacing-m4/source-commit) · [Combined M4 receipt](https://github.com/tolgraven/tolglow/tree/3b32f5425f0cbdf75f234626b8359f53ec4ea262/cadence/weighted-combined-dmx-m4)

## Files

- [Comparison still](next-slot-recovery.png) and [slow-motion trace](next-slot-replay.mp4)
- [Released trace](released-4f65f06c.json) and [forward-port trace](candidate.json)
- [Released tests](baseline-tests.log) and [forward-port tests](candidate-tests.log)
- [Injected-clock replay](replay.clj), [focused test runner](run-tests.clj) and [media renderer](render-replay.py)

For each Afterglow checkout, resolve the project test classpath with `lein with-profile +test classpath` and invoke `clojure.main` with that classpath and either Clojure file. Save the replay output to the corresponding trace filename. Run `python3 render-replay.py` with Pillow and FFmpeg available to regenerate the still and video.
