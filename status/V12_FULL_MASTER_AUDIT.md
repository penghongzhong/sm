# W20 v12 full-master audit

Authority: synchronized W20 Library manuscript, with the private `section2-strict-sync` source used only to expand proofs that are compressed in the current Library edition.

## Node status

| Node | Exact role | Status |
|---|---|---|
| `v12:lem:coeff` | coefficient reconstruction/budget | GREEN: public Lean kernel + source audit + machine-green baseline |
| `v12:lem:electric` | temporal curvature divergence identity | GREEN at algebra/interface level; standard product-rule bridge registered |
| `v12:lem:chart-hodge` | explicit chart curvature + Coulomb-Hodge reconstruction (strict source) | YELLOW/GREEN split: chart algebra and Hodge symbol kernels compile; full Schwartz Fourier injectivity is registered standard analysis |
| `v12:lem:low-curv` | low-frequency curvature budgets (strict source) | YELLOW/GREEN split: constants compile; Plancherel/multiplier interface registered |
| `v12:lem:sampling` | Hilbert-valued band-limited sampling | YELLOW: paper constant kernel added; Hilbert FTC/trace + Plancherel derivative bound are standard-analysis interfaces |
| `v12:prop:axial` | cell axial gauge identities + square budgets | YELLOW: exact proof decomposed into FTC, sampling, Bernstein, curvature budgets; dedicated paper-specific kernel still to be added |
| `v12:lem:lattice` | legal mixed-norm square localization/synthesis | YELLOW: standard vector-valued Minkowski/Cauchy-Schwarz; exact finite-family interface to be registered |
| `v12:prop:countermodel` | failure of exchanging outer suprema with cell l2 | RED/YELLOW: explicit construction is internal; finite combinatorial/smooth translation model still needs exact formal map |
| `v12:thm:IMS` | covariant IMS isometry/projection/operator/energy identity | YELLOW: paper cancellation kernel added; standard product/chain rule + finite-sum operator interface remains |
| `v12:cor:IMS-forcing` | exact source synthesis | YELLOW: algebra kernel added; depends on full IMS operator map |
| `v12:thm:relative` | two-background relative connection formula | YELLOW: first- and second-order algebra kernels added; product-rule/operator realization remains |
| `v12:cor:relative-cocycle` | unitary overlap cocycle + true L2 difference | YELLOW: phase identities added; unit-modulus/L2 partition interface remains |
| `v12:thm:closure` | strong-local-limit closure of Coulomb constraints/evolution | RED/YELLOW: requires explicit standard compactness/weak-convergence interfaces plus paper-specific nonlocal Hodge tail argument |
| `v12:thm:tightness` | frequency tightness -> local strong compactness | RED/YELLOW: requires fixed-frequency time regularity + Arzela-Ascoli/diagonal compactness interface |

## Current v12 cut-set

The shortest remaining path to complete v12 is:

1. finish `sampling` standard-interface registration;
2. close `axial` from sampling + curvature + Bernstein;
3. register mixed-norm lattice theorem;
4. formalize the countermodel's finite lower-bound core;
5. close IMS/relative operator-level interfaces;
6. formalize/source-type the two compactness theorems `closure` and `tightness`.

Only after all of these are exact statement mappings may v12 be marked full-master GREEN.
