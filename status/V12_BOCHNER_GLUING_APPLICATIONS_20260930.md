# Exact Bochner and measurable-gluing applications

These are application proofs, not new axioms or interfaces asserting internal
conclusions. Run 148 checked the first Bochner/compatibility batch and found
elaboration errors; its dependent modules did not compile. The corrections
and cutoff realization extensions remain candidates pending the next run.

## Standard sources and their concrete use

All declarations below come from pinned Mathlib
`a98628e16c11f5167f16124105ddce53efa9bfe5`.

- `MeasureTheory/Measure/SeparableMeasure.lean`, `Lp.SecondCountableTopology`:
  requires a separable measure, separable normed target, 1 <= p < infinity;
  concludes second countability of Lp. The instance here is spatial Lebesgue
  measure on EuclideanSpace R (Fin 2), target EuclideanSpace C (Fin 2).
- `MeasureTheory/Measure/Prod.lean`, `Measurable.lintegral_prod_right'`:
  S-finite inner measure and measurable nonnegative extended-real integrand
  give measurability of its parameter integral. YMeasurableLpSections applies
  it to the p-th power of the distance from the SAME raw field to a measurable
  representative of a fixed spatial Lp element.
- `Topology/Bases.lean`, `isOpen_iUnion_countable`: second countability makes
  an open union equal a countable subunion. The candidate proves directly
  that measurable distances to fixed points imply measurability, using this
  countable ball cover. Lp-valued measurability is not an assumption.
- `MeasureTheory/MeasurableSpace/MeasurablyGenerated.lean`,
  `Filter.Eventually.exists_measurable_mem`: a.e. representative identities
  contain a measurable full-measure set. Raw functions and Lp classes are
  both set to zero off this SAME set. This addresses exceptional times
  without asserting that a.e. spatial Lp membership holds at every time.
- `MeasureTheory/Measure/Prod.lean`, `lintegral_prod`, and
  `Function/LpSeminorm/Defs.lean`, `eLpNorm_eq_lintegral_rpow_enorm_toReal`:
  Tonelli and finite nonzero exponent norm formulas give the exact identity
  between the time-Lp norm of spatial-Lp classes and the raw spacetime-Lp norm.
  YTBochnerSectionNorm constructs the classes; its actual-source theorem
  applies this to F_j=A_j q and G=Vq+W conjugate(q), retaining Holder bounds.
- `Function/LpSpace/Basic.lean`, `Lp.LpToLpOfMeasureLeSMul` and its coeFn
  theorem: a finite measure domination gives a continuous restriction map
  with the SAME a.e. representative. YLocalLimitCompatibility supplies
  domination constant 1 from explicit nested cylinder radii, proves restriction
  composition, and uses uniqueness of the same sequence's limit.
- `Function/StronglyMeasurable/AEStronglyMeasurable.lean`,
  `AEStronglyMeasurable.iUnion`, `stronglyMeasurable_mk`, `ae_eq_mk`:
  the least containing cylinder chooses a raw representative, countably many
  proved a.e. compatibility identities identify it with every local limit,
  and a global strongly measurable representative is then chosen. No gluing
  or compatibility conclusion is supplied as a hypothesis of the final theorem.

## Source identities at exceptional times

The raw compact-test FTC uses the actual smooth time derivative at every
interior time. Identification with the Lp-valued source only needs to hold
a.e. in time, since both source integrability and the interval integral are
invariant under a.e. equality. A local revision of ZF/ZG replaces their former
all-interior-time F/G representative premises by a.e.-time premises. The
endpoint Q representative remains an every-time equality and is justified by
the Fatou/energy construction. This broadens the lemma's applicability; it does
not weaken the original paper's theorem or suppress a required endpoint.

## Further cutoff realization candidates

YVGlobalCutoffRepresentative exhausts the previously verified local-ball
Fourier/convolution identity, obtaining a global a.e. representative for
arbitrary L2 input. YWSpacetimeCutoffRealization derives joint measurability
by continuous BCF evaluation, derives spacetime L2 from the exact Bochner
norm identity, and constructs every local cylinder representative. This removes
a representative-equality assumption for the constructed actual cutoff.

The original Hodge coefficient estimates and exact original-PDE instantiation
remain upstream; these candidate applications do not certify Theorems 7.2/7.1
or later scattering statements.

## Run 149 evidence and next batch

Commit 15dd0bc0c218ecb06191b523c00dfbe2807a4e4d, Run 149
(36745397232), completed with failure. YLocalLimitCompatibility and
YVGlobalCutoffRepresentative compiled; the revised ZF/ZG a.e.-time source
statements also compiled. Measurable gluing needs classical decidability
for Nat.find. Lp section measurability needs explicit pointwise subtraction
before eLpNorm_congr_ae. The blocked Bochner norm / cutoff / energy modules
are not certified.

The next batch repairs these two roots and submits actual canonical cutoff
classes, raw slab realization, and fixed-frequency compactness from the raw
PDE. The latter constructs hIntegral, hRep and hBudget internally. Its
upstream raw-system/Hodge/MZ applications remain open. All new declarations
remain candidates until an actual successful run.

## Run150 update

YMeasurableLpSections, YMeasurableLocalLimitGluing and YUEveryTimeBochnerEnergy
compile with only propext/Classical.choice/Quot.sound. Exact Fubini norms still
failed in YT; no downstream same-field slab/compactness PASS claim.
Next leaves use Mathlib.MeasureTheory.Function.Holder:
ContinuousLinearMap.holder/coeFn_holder/holderL for actual L2 x L2 -> L1
products and strong convergence. The paper-specific source/product definitions
and exact a.e. representatives are explicit; no product convergence interface.
ContDiffBump (inner radius1, outer2) and HasCompactSupport.toSchwartzMap construct
the auxiliary test cutoff, discharging its hypotheses inside the common-limit
connection. Original Hodge reconstruction and M/Z estimates remain open.

## Run151 update and new closure applications

YT exact norm/source realization and YX actual raw slab representation compile.
The original statements and source exponent assumptions are retained.
YW unfolding, YZ continuity lemma name and drift-product heartbeat need repairs.

New candidates define the actual rotation (-x_2,x_1), kernel
K(x)=(2*pi*norm(x)^2)^(-1) times that rotation, including value0 at0.
The kernel norm and far-field integrability/bound are proved, not assumptions.
For the near kernel, Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean
`integrableOn_ball_of_norm_le_rpow` assumes a finite-dimensional real Haar
space, dim>=1, singular exponent alpha<dim, a.e. power domination and strong
measurability. The concrete application proves dimension2, alpha=4/3<2,
actual kernel measurability and exact power domination; it yields the truncated
kernel in L^(4/3). Near-field Young convergence/interpolation remain open.

The quadratic local-limit candidate uses actual coordinate projections,
complex conjugation, Holder products, real/imaginary parts and coefficient4/2
to realize B,S,m,W. It proves L1 convergence from L2 convergence and exact
a.e. representatives. No quadratic convergence is an interface premise.

## Run152 actual connection evidence

YW, YZRawSourceTimeBounds, ZI and ZJ compile, including the full raw-divergence
PDE-to-common-measurable-limit chain. Remaining concrete hypotheses are visible
in the declarations, not hidden interfaces. Original Hodge/MZ and nonlinear
closure still need proof. New raw-tail identification and raw-source common
limit candidates remove the supplied time-Lp objects; a separate zero-length
slab proof prevents silently excluding degenerate finite intervals.

## Actual Hodge/closure continuation (Run154 pending)

The compactness endpoint ZL starts with the original i*dt+Laplacian Coulomb
PDE and proves the drift rewrite; it constructs all source-time classes via
ZK, then invokes compiled ZJ/ZI. Its coefficient MemLp/budget assumptions
still require the original Hodge/MZ proof. The frequency-tail assumption is
explicit in original Theorem7.2 and may be retained. Full7.2 also requires7.1.

Forward dependency order for7.1:
1. Raw local L2 convergence -> actual B,S,m,W strong local L1 (YQuadratic).
2. Actual |B|<=2|Q|² -> spatial L1 and spacetime L2 budgets (YR).
3. Exact Hodge kernel -> far integral bound (YHodgeFarField PASS153),
   curvature-budget substitution (YS candidate), near kernel L^(4/3)
   (YHodgeNearKernel repair pending).
4. Near kernel Young: YIYoungConvolution constructs Lp-valued Bochner integral,
   proves its Young budget, and proves raw convolution L1/AE existence.
   **Raw convolution = constructed Lp class remains OPEN.** Neither is assumed
   interchangeable. Time L1/Linfinity -> Lp convergence remains OPEN.
5. YHodgeInterpolation candidate derives ||f||2²<=||f||43||f||4 and strongL2
   from strongL43 plus uniformL4. Actual Hodge HLS/MZ L4 bound remains OPEN.
6. YNonlinear drift product and YWeakStrongProducts handle actual product
   integral limits. The latter requires the weak coefficient limit separately.
7. YPDenseTestExtension candidate proves dense-test extension under uniform
   operator bounds. Concrete density, actual local test limits, Riesz operators,
   preserved M/Z bounds and distributional closure remain OPEN.

The new interpolation, Young, dense-extension and weak-strong files are
uncompiled candidates until a later actual run. No full7.1/7.2 label is green.
Reverse audit: the original closure theorem cannot bypass3-7 by importing a
conclusion-valued interface; its reconstructed coefficients must be the same
fields in the PDE and raw Hodge formulas. All later full-theorem branches
remain uncertified until these and their own dependencies are checked.


## Run156 superseding update

Run156 actually checked 86/90 files. YHodgeInterpolation, YIYoungConvolution,
YPDenseTestExtension, YQuadraticLocalLimits, YRActualCurvatureBounds,
YSActualHodgeFarBounds and YHLSExternalStatement now PASS. The earlier
candidate labels above are historical. YHodgeNearKernel already passed154;
YNonlinearLocalProducts and YWeakStrongProducts passed155.
Raw Young equality, finite-time upgrading and vector fractional domination
have three root errors repaired in the next batch; actual HLS application
remains import-blocked until that run. Inherited bounds, concrete compact
Lp-test density, actual Fourier Riesz operators and mixed/Hodge budgets
are new uncompiled candidates. Whole7.1/7.2 remains OPEN.


## Run157 superseding update

93/96 files actually passed. YJYoungRawRepresentative, YKBoundedTimeUpgrade,
YPCompactTestDensity, YSCurvatureMixedBounds, YSHodgeFractionalDomination,
YTHodgeHLSApplication and YUHodgeEnergyL4Application PASS. YO exhaustion
filter and YRiesz operator API repairs remain candidates; YPInheritedEnergy
was import-blocked. New YQWeakClosureFromLocal and YRTensorWeakClosure derive
actual weak integral convergence from local strong convergence and budgets;
YSCoulombRieszTimeOperator and YVHodgeSpacetimeBudget are uncompiled.
Reverse audit: global Hodge MZ, spacetime Riesz realization, near/far strong
Hodge convergence, all actual zero-order coefficients, and distributional
closure must still be connected before marking full7.1 or full7.2.


## Run158 superseding update

97/100 actually passed. YOInheritedBounds, YQWeakClosureFromLocal,
YRieszCoulombOperator and YSCoulombRieszTimeOperator PASS. Inherited energy,
tensor weak raw representative and spacetime Hodge ENNReal power proof have
specific compilation repairs in the next batch. Same-field near/far and
Young convergence candidates now derive density hypotheses from original
Q local strongL2 convergence and energy; these have not been run yet.

Remaining reverse application obligations include the joint spacetime
representative for time-lifted Riesz outputs and exact S/A0/V/W reconstruction,
original fields' measurability on the restricted time interval (no stronger
unmentioned global regularity assumption), final near/far strongL2 convergence,
and testing every original constraint and PDE. Full7.1/7.2 stays OPEN.

Run159 actual check:103/110, FAILURE. Energy/tensor weak closure/full-dual
conversion/Hodge spacetime MZ/exact near-far/approximation limit PASS.
Same-field local Hodge convergence and Fubini isometry/surjectivity plus
joint spacetime Riesz are unverified next-batch candidates. Reverse audit:
full nonlinear coefficient reconstruction and distributional PDE closure
remain prerequisites of7.1/7.2; no whole-theorem label changed to green.

Run160 actual check:103/115, FAILURE. No new green files. Five roots plus
seven missing-import failures. Next candidates add actual S/m/A0/W and V
weak limits and A_j Q strong product, with own concrete hypotheses derived.
Reverse obligations remain: compile the roots and applications; identify
real Fourier outputs; build compact smooth distributional tests; pass the
original constraints/PDE to the limit; connect full7.1/7.2, then later branches.

Run161 actual check:109/120, FAILURE. Six new files PASS, including actual
curvature cutoff and Young spacetime convergence, W/mass and drift budgets,
near/far error, and generic Lp sections. Five new roots and six blocked imports
remain. Fourier-real correspondence and concrete compact-test source limits
are submitted next, not counted as coverage. Reverse obligations unchanged:
exact same-field reconstruction, distributional closure, full7.1/7.2 and all
later theorem branches. Private v15 remains the current synchronized text.

Run163 actual check:117/126, FAILURE. Fubini onto/equivalence and original
Hodge local L43/L2 limits PASS. Five direct roots/four imports remain.
Run164 adds exact same-Q A0 sections and local-domain smooth compact IBP,
original scalar PDE tests and actual drift/zero-order test limits; candidates
remain unverified. No new external schema or private manuscript file.

Run164 actual check:122/131, FAILURE. Joint spacetime Riesz, norm-square
weak closure, actual drift strong L1, scalar/W compact tests and vector
drift derivative tests PASS. Three direct roots/six imports remain.
Run165 candidates add original slab extension/MZ, actual source L43 testing,
full actual PDE distributional passage and original first-order compact
constraints. Full7.1/7.2 remains OPEN; candidates are not green.

Run165 actual check:123/136, FAILURE. Full spatial Fourier reality module
PASS. Four direct roots/nine imports remain. Run166 repairs and actual
spatial-constraint closure applications are candidates, not green.

Run166 actual check:129/141, FAILURE; three direct roots/nine imports.
NEW PASS: YFFFiniteSlabMeasures, YWSmoothSlabExtension, YZZGLocalSmoothIntegration,
YZZLScalarDriftTest (including ordinary scalar AQ tests), YZZPCurvatureTestLimits,
YZZQActualConnectionTests. These replace only their own previous candidates.
Next batch adds original slab derivative preservation, canonical coordinate
chain rules, original A0/V representatives and internally derived A/V/W budgets,
then ZM same-Q common-subsequence application. All additions remain candidates.
Original physical geometry/gauge hypotheses and full7.1/7.2 remain OPEN.
