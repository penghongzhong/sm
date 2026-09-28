# T023–T024 causal closure audit

Verification authority: synchronized W20 manuscript.

## T023 — relative WMB recurrence

Paper node: `v13:lem:relative-WMB`.

The proof contains no new PDE theorem beyond WMB13:
- first Bony ordering `R_r P_s ∇P_k`: apply the already closed WMB13 product estimate to `R_r P_k`;
- second ordering `P_r R_s ∇P_k`: use the already source-audited background product estimate;
- use the exact scale cancellation from T009;
- sum the `r,s` indices by Cauchy-Schwarz and discrete `l^1` Young;
- close the mixed square-root term with `2ab <= a^2+b^2`.

The current Lean theorem T023 formalizes the final scalar closure from the pre-summed recurrence.  Its pre-summed recurrence is therefore reducible to already certified WMB/background estimates plus standard sequence analysis.

Classification: **T023 SOURCE-REDUCED; no new internal theorem.**

## T024 — causal slow-envelope accumulation

Paper node: `v13:lem:causal-linear`.

Starting from the weak-linear slow-envelope bound, split the convolution at
`j <= K+D` and `j > K+D`.

- near part: standard `l^1 * l^2 -> l^2` Young;
- far part: factor
  `2^{-delta(j-k)} = 2^{-delta D/2} 2^{-delta(j-k)/2}`;
- apply Young and square.

No Schrödinger-map structure remains in this step.

Classification: **T024 STANDARD SEQUENCE ANALYSIS.**

## v13–v14 cut-set status

After the source audits of T003, T007, T008, T014, T018, T020, T023, and T024, every analytic hypothesis appearing in the current T004–T025 migration spine is classified as one of:

1. an exact Smith 2013 published input;
2. a standard harmonic-analysis theorem (Coifman-Meyer, HLS, Riesz/LP/Hölder/Bernstein, sequence Young/Cauchy-Schwarz);
3. an earlier internal manuscript node whose finite algebra/connector is separately Lean-checked.

The remaining work for this range is:
- tighten paper-specific scalar theorem parameters into generic source-typed interfaces where practical;
- obtain fresh machine compilation of the repaired migration batch;
- continue the same semantic audit through T026–T033.
