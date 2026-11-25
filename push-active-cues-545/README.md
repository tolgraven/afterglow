Presentation of the recorded virtual Push 2 MIDI output and in-memory rendered DMX. Separate running launches of Ember appear as distinct pads. The operator selects one active launch, enters reorder mode and moves it after Ice. The effective order changes from [0:1 0:2 0:3] to [0:2 0:3 0:1]. The dimmer byte changes from 255 to 209.

The evidence originated at Afterglow a5a21bdc. The same trace was replayed byte for byte at 15e257b8, including the shared group-opacity hooks. The additional exact-head run applied a half-opacity factor to the reordered contribution and verified both order and output.

[Still](active-cue-order.png) · [Short replay](active-cue-order.mp4) · [Original capture data](replay.json)
