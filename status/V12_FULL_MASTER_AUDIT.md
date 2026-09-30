# W20 v12 full-master audit

> **Historical audit — certification withdrawn.** The GREEN labels and
> whole-block conclusions below record an earlier, insufficient standard of
> evidence. They are not current full-statement certificates. See
> `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
> `WHOLE_PAPER_COVERAGE.md`; actual objects, internal proof steps and concrete
> external-theorem hypotheses must still be checked against the full manuscript.


Authority: synchronized 133-page W20 Library manuscript
`stereo_scalar_scattering_v20_W20_LeanSync_v1`.

Verification foundation: Mathlib logic/standard analysis, plus the exact
standard-analysis interfaces registered in `V12_STANDARD_INTERFACES.md`.
No downstream scattering/profile conclusion is used as a v12 input.

## Machine result

GitHub Actions Run **#25** (`36415082616`) concluded **SUCCESS** on
`whole-paper-lean` after compiling the complete public corpus containing the
new v12 kernels.

The forbidden-placeholder scan also passed.

## Exact 12-node v12 target

| W20 node | Certification |
|---|---|
| `v12:lem:coeff` | GREEN — coefficient kernel + HLS/Plancherel source boundary |
| `v12:lem:electric` | GREEN — covariant product-rule cancellation + electric algebra kernel |
| `v12:lem:sampling` | GREEN relative S1/S2 — Hilbert FTC/trace + band-limited Plancherel; paper constant kernel compiled |
| `v12:prop:axial` | GREEN relative S1/S2 — FTC/sampling/Bernstein; scale-budget kernel compiled |
| `v12:lem:lattice` | GREEN relative S3 — vector-valued Minkowski/Cauchy-Schwarz; partition kernels compiled |
| `v12:prop:countermodel` | GREEN relative S4 — smooth translation/Fourier support/Schwartz separation; finite many-cell growth kernel compiled |
| `v12:thm:IMS` | GREEN relative S5 — product rule/local finite sums; exact cancellation/energy kernels compiled |
| `v12:cor:IMS-forcing` | GREEN — direct composition of IMS and `T^*T=Id` |
| `v12:thm:relative` | GREEN relative S5 — first/second covariant derivative algebra kernels compiled |
| `v12:cor:relative-cocycle` | GREEN relative S5 — exponential cocycle/difference kernels compiled |
| `v12:thm:closure` | GREEN relative S6 — standard weak/strong/distribution convergence; paper Hodge-tail/product bookkeeping kernels compiled |
| `v12:thm:tightness` | GREEN relative S7 — fixed-frequency regularity + Arzela-Ascoli/diagonal extraction; exponent/Cauchy kernels compiled |

## Supporting strict-Section-2 nodes

The private strict proof source also isolates chart-Hodge reconstruction and
low-frequency curvature budgets as separate support lemmas. Their public
stereographic/Hodge/Plancherel/low-frequency kernels are machine-green, even
though the current 133-page Library edition does not number them as separate
theorem environments.

## v12 conclusion

Under the user's declared foundation (standard analysis + exact published
external results), the **v12 proof-bearing block is GREEN: 12/12**.

This is not a claim that Mathlib has re-proved every generic theorem such as
Arzela-Ascoli or Hilbert-valued FTC from first principles. It means every
paper-specific v12 step has been isolated and machine-checked and every
remaining generic step is explicitly registered in S1-S7.

The next exact full-master block is v13.
