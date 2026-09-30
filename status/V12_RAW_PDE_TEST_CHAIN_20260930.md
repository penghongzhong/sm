# Raw PDE / compact-test chain: exact boundary

## Completed evidence

Run 147 / 36742383395 / job 109979814233 checks
`e8833f6e69ffe6beec99a305d596719b78ed6d1e`.
ZA–ZH, YC and YSpacetimeSlices COMPILE_OK; printed axiom dependencies are
standard-only. YLocalLimitCompatibility failed on radius-cast inference;
gluing was dependency-blocked. Whole run FAILURE (59/61 files passed).
Next batch repairs those casts and submits YMeasurableLpSections,
YTBochnerSectionNorm, YUEveryTimeBochnerEnergy. These prove measurability,
exact same-field norm transfer, actual source classes and every-time energy
Bochner realization; their status is pending compiler verification.

## Forward and reverse correspondence

| Module | Proved/candidate conclusion | Actual inputs still required |
|---|---|---|
| ZA (passed) | first/second test derivative L2 limits; full source L1 limit | compact smooth cutoff, value 1 at zero, range [0,1], actual time-Lp fields |
| ZB (passed) | the limiting source is the exact cutoff source | same fields and cutoff kernel as ZA |
| ZC (passed) | compact test IBP twice and actual raw PDE tested source | smooth raw q,f; continuous g; actual pointwise divergence PDE |
| ZD (passed) | raw tested curve continuity and FTC | joint raw q,dq continuity through endpoints, actual time derivative in interior |
| ZE (passed) | Lp source equals the raw tested PDE source | exact a.e. representatives of q,f,g, same test |
| ZF (passed) | finite-test source integrability and time identity | above raw PDE/regularity/representatives; no tested identity input |
| ZG (passed) | actual cutoff BCF time integral identity | above conditions, Q time-L∞, F time-L2, G time-L4/3, endpoint Q representatives |
| YC, ZH (passed) | product derivative, Coulomb divergence cancellation and raw RHS conversion | actual differentiability and div A=0 at the same spatial point |

The compiled ZG theorem accepts no hIntegral, hFTC, hCompact, kernel derivative
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

The new compatibility/gluing candidates are in YLocalLimitCompatibility and
YMeasurableLocalLimitGluing. They derive nested equality and one strongly
measurable raw field from the SAME sequence's local L2 limits. They do not
assume compatibility or gluing, and do not certify the original PDE instance.
