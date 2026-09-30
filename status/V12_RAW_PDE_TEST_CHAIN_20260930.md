# Raw PDE / compact-test chain: exact boundary

## Completed evidence

Run 145 / 36739627738 / job 109970305733 checks
`be918a692f80a1c7440f76d96f9a9a2868895a6b`.
ZA–ZD COMPILE_OK, all printed declarations use only propext,
Classical.choice, Quot.sound. ZE FAIL at an unspecified measure parameter;
ZF–ZG dependency-blocked. Whole run FAILURE (53/56 files passed).
Next batch repairs that measure and submits YC, YSpacetimeSlices and ZH.
This file does not certify those pending modules.

## Forward and reverse correspondence

| Module | Proved/candidate conclusion | Actual inputs still required |
|---|---|---|
| ZA (passed) | first/second test derivative L2 limits; full source L1 limit | compact smooth cutoff, value 1 at zero, range [0,1], actual time-Lp fields |
| ZB (passed) | the limiting source is the exact cutoff source | same fields and cutoff kernel as ZA |
| ZC (passed) | compact test IBP twice and actual raw PDE tested source | smooth raw q,f; continuous g; actual pointwise divergence PDE |
| ZD (passed) | raw tested curve continuity and FTC | joint raw q,dq continuity through endpoints, actual time derivative in interior |
| ZE (measure repair pending) | Lp source equals the raw tested PDE source | exact a.e. representatives of q,f,g, same test |
| ZF (dependency-blocked) | finite-test source integrability and time identity | above raw PDE/regularity/representatives; no tested identity input |
| ZG (dependency-blocked) | actual cutoff BCF time integral identity | above conditions, Q time-L∞, F time-L2, G time-L4/3, endpoint Q representatives |
| YC, ZH (submitted candidates) | product derivative, Coulomb divergence cancellation and raw RHS conversion | actual differentiability and div A=0 at the same spatial point |

The ZG candidate accepts no hIntegral, hFTC, hCompact, kernel derivative
limit or source L1 limit: these are derived using the preceding chain.
Its raw regularity, representatives and Bochner hypotheses must be instantiated
for the original reconstructed fields. They are not externally licensed facts.
Reverse audit: cylinder compactness still requires the same-field local L2
representative identity and uniform source/energy budgets; the common
subsequence/gluing and full Theorems 7.2/7.1 are not closed by this chain.

## Standard analysis declarations actually used

Mathlib pin `a98628e16c11f5167f16124105ddce53efa9bfe5`:

* `Analysis/Calculus/LineDeriv/IntegrationByParts.lean`,
  `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`:
  finite-dimensional real space with Haar measure; integrability of both
  differentiated products and the undifferentiated product; differentiability
  on the relevant supports. Conclusion: integral f D_v g = -integral D_v f g.
  ZC proves the integrabilities from compact support and smoothness, applies
  the theorem once/twice, and checks the signs and actual source coefficients.
* `MeasureTheory/Integral/Bochner/Set.lean`,
  `continuousOn_integral_of_compact_support`: measure finite on compacts,
  fixed compact support uniform in the parameter, joint continuity on
  parameter-set × space. Conclusion: continuity of the parameter integral.
  ZD supplies tsupport ψ and proves the integrand vanishes outside it.
* `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`,
  `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`: ordered endpoints,
  continuity on the closed interval, derivative on the open interval and
  interval integrability of that derivative. Conclusion: FTC equality.
  ZD proves each premise for the tested raw curve, including endpoints.
* `Analysis/Calculus/FDeriv/Mul.lean`, `fderiv_fun_smul`:
  differentiability of the scalar and vector factors at the same point;
  conclusion: the Frechet derivative product rule. YC evaluates this at
  the actual spatial basis vectors and uses div A=0 by additive algebra.

These are proved library declarations, not newly introduced axioms.
No external PDE theorem has been added as a substitute for an internal step.
Public files contain no private manuscript text, TeX or PDF.

YSpacetimeSlices also submits actual a.e. Lp sections and exact scalar power
integral Fubini results. It does not infer Bochner measurability or an
every-time representative from an a.e. assertion. Its standard source is
Mathlib MeasureTheory/Integral/Prod.lean: Integrable.prod_right_ae,
AEStronglyMeasurable.prodMk_left, Integrable.integral_prod_left and integral_prod;
MemLp.integrable_norm_rpow supplies the checked finite exponent integrability.
