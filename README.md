# Packed spatial position filtering

These captures illustrate a synthetic rig of 20,000 RGBW pixels and 64 moving heads. Fixtures are sorted by X. The packed lookup checks Y and Z before fetching the original row for the exact shape test. This affects fixture selection for spatial fields and preserves the original row order and types.

The warm CPU comparison used original Afterglow `591ef03a` and packed prototype `fba5d08f` over four moving spatial fields. CPU p50 was 9.901 to 8.033 ms and p95 was 14.893 to 10.765 ms. The candidate left warm median allocation broadly similar. This is a query-stage comparison on shared Linux.

The first-build comparison used `fba5d08f` and final builder `ed764b71`. CPU p50 was 8.739 to 1.343 ms and allocated bytes per build were 10,784,944 to 321,248. A repeat placed median first-query CPU at 10.398 to 3.565 ms. Both builders retain 321,024 bytes for the dense rig. The final builder can briefly allocate the columns on a mixed-number rig before selecting the scalar path. Warm measurements varied across builder trials that ran the same query code.

The full replay compared `591ef03a` with `ed764b71`. It matched model, intent and membership digests, positional weight bits, 69,076,272 compact bytes, and 3,792 complete ArtDMX packets across 24 frames and a repatch in each scenario. The 25 ms step was a replay clock. Sustained fresh 40 Hz remains unverified by this test. The production candidate `83606deb` carries the same spatial and test blobs on current Afterglow master.
