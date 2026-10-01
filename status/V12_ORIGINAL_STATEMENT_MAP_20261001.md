# Exact original-statement map (not a full-theorem certificate)

## Theorem 7.1 — original local closure

The private original statement retains: finite closed slab; smooth genuinely
compatible sequence with coefficients reconstructed from that same sequence;
uniform mixed L-infinity(time)/L2(space) bound M and spacetime L4 bound Z;
strong local L2 convergence on every real-radius cylinder.

Candidate entry: V12_YZZWClosedSlabLocalClosure,
`v12_closed_slab_original_local_closure`.

| Original node | Concrete Lean object / derivation | Actual status |
|---|---|---|
| Closed-slab field | qn with closed continuity and open ContDiffOn | Original smoothness unpacking, reader audit pending |
| Original compatibility | V12CanonicalSpatialDistributionalConstraints | Literal original divergence/curl/torsion test equations; SE extension and U limit are candidates |
| Original advective PDE | V12OriginalScalarDistributionalPDE | Original test definition, not derived divergence equation; GR derives latter (PASS171) |
| Same-field A0 | v12_actualTemporalCoulombL2 | YSFB spatial Riesz-section formula PASS170 |
| Same-field V | v12_originalReconstructedPotential | BZ extension representative candidate, no continuity of A0 assumed |
| Same-field W | v12_WDensity | Existing explicit quadratic formula |
| Actual source-class equality | v12_originalScalarSource | KT candidate uses AE coefficient equality and local equality of derivatives |
| Coefficient/source budgets | Hodge MZ and temporal Riesz L2 | Existing verified budgets, J summation PASS172 |
| Strong global measurable limit | Local L2 exhaustion then measurable representative | Existing gluing lemmas; V/W application pending |
| Same M and Z for limit | v12_global_energy_inherited and v12_global_budget_inherited_from_local_L2 | Existing verified lemmas; V/W application pending |
| B, A, AQ on every real-radius cylinder | V12SameFieldRealCoefficientConvergence | SD/SF candidates; AQ finite norms must be proved before toReal squeeze |
| Limit PDE and constraints | Canonical explicit compact-test predicates | NE/U/V/W candidates; not yet full7.1 PASS |

The integer-cylinder hypotheses in W follow immediately by specializing the
original all-real-radius assumptions at R+1. Its output gives all real radii.
The representative v agrees with the original limit u almost everywhere, so
the claimed function-space conclusions concern exactly the original Lp class.
No source-convergence, hIntegral or hCompact conclusion is a W premise.

## Theorem 7.2 — frequency tightness to common strong limit

ZL's fixed-frequency compactness, common subsequence and measurable gluing
are compiled, but its original-data application ZM still requests spatial
smoothness of A, continuity of V and closed-slab continuity of the time
derivative. Those additional conditions have not been discharged from the
literal original definition. Do not promote the ZM assembly to full7.2.

The original-distribution route now has a complete CANDIDATE dependency chain:
GS concrete tensor tests (PASS172); GT/GU/GV/GW tensor PDE, Fubini, weighted
time source; ZDE/ZDF residual uniqueness/source identification (pending173);
ZDG same-Q MZ instantiation; ZDH actual vector FTC; ZES exact Q/F/G class
match; ZFS compact Lp time identity; ZGS cutoff source/endpoint limits;
ZIS fixed-frequency compactness; ZKS common sequence and measurable gluing;
ZKT closure on that SAME subsequence. ZKS treats zero/empty slabs separately.
GS PASS172; GU/GV/ZDD/ZDE PASS173. Other new applications remain candidates. ZKT is NOT a certificate.

Reverse audit: ZKT's inputs are closed continuity/open smoothness of qn,
actual L4 membership and original M/Z bounds, literal spatial compatibility,
literal original advective distributional PDE, and actual raw-frequency
norm tightness. It has no input for hIntegral, hCompact, Q/F/G representatives,
coefficient bounds, source convergence, local limits or global qn measurability.
ZKT obtains a common local limit through ZKS, then instantiates W on qn∘σ.
ZDG derives all internal local-integrability obligations from original MZ.
No A0 continuity or A smoothness is added along this route.

Forward audit: ZKS constructs actual time Q/F/G through YZRawSourceTimeBounds,
using CAOriginalReconstructedBudgets for A,V,W. Scalar tested source is joined
to vector source in ZDH and identified with exact Lp kernels in ZES; ZGS uses
the already verified concrete cutoff/test norm limits. No norm-only field
identification substitutes for AE equality. These applications require CI.

Fourier normalization: v12_cyclicScale N = 2*pi / 2^N already matches
xi=2*pi*eta. YFourierKernelNormalization explicitly proves the inverse-integral
Jacobian. Its local-F unfolding correction PASS173.
Literal manuscript/Lean Fourier-profile application must be checked together
with the full theorem, even though the source/compactness statements use the
actual existing cutoff definition directly.

## Foundations / acceptance

Retained external proposition: V12ExternalHLS2D, Tao, An Epsilon of Room I,
Corollary1.11.18; precise hypotheses and conclusions in the source registry.
All other cited support here is the pinned Mathlib or previously compiled
project lemmas. Original load-bearing conclusions are never external axioms.
Full7.1, full7.2 and later paper branches remain OPEN. Compilation counts
are not coverage of the 207 original proof-bearing statement environments.
