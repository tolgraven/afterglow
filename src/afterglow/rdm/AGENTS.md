# RDM protocol

Keep OLA RPC and direct Art-Net gateway I/O behind the job-owned connection in `transport/open!`. Both transports return the same discovery table and E1.20 response maps. The transport owns reply correlation and overflow assembly. Shared command handling owns delayed acknowledgements and NACKs.

Exercise direct gateway changes with the loopback UDP fixture and independent wire vectors. Test cancellation, deadlines and address/transaction mismatches. Applications own discovery jobs, fixture registry changes and persistence. Document visible protocol behavior in `doc/architecture/physical-output.md`.
