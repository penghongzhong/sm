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
