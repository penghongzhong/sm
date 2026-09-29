import Mathlib

/-!
v12:thm:tightness -- cutoff limits, a common extracted subsequence, and
actual Bochner L2 spaces on finite spacetime cylinders.

The final theorem below is conditional on uniform cutoff-tail control and
compactness of each fixed localized cutoff range. It proves, rather than
assumes, a SINGLE subsequence working for all integer radii and cutoffs.

Remaining PDE work: define P as the manuscript's spatial Fourier cutoff,
prove fixed-cutoff compactness from its space/time estimates, derive slab
MemLp from M, and glue the compatible local limits. No full PDE certificate
is asserted by this module.
-/

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_cauchy_of_uniform_cutoff
    {X : Type*} [MetricSpace X]
    (u : ℕ → X) (v : ℕ → ℕ → X) (err : ℕ → ℝ)
    (hErr : Tendsto err atTop (𝓝 0))
    (hApprox : ∀ k n, dist (u n) (v k n) ≤ err k)
    (hCutoff : ∀ k, CauchySeq (v k)) :
    CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hErr (ε / 3) hthird
  have habs : |err k| < ε / 3 := by
    simpa [Real.dist_eq] using hk k le_rfl
  have he : err k < ε / 3 := lt_of_le_of_lt (le_abs_self _) habs
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hCutoff k) (ε / 3) hthird
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmiddle : dist (v k m) (v k n) < ε / 3 := hN m hm n hn
  have hleft := hApprox k m
  have hright : dist (v k n) (u n) ≤ err k := by
    rw [dist_comm]
    exact hApprox k n
  have ht1 := dist_triangle (u m) (v k m) (u n)
  have ht2 := dist_triangle (v k m) (v k n) (u n)
  linarith

theorem v12_limit_of_uniform_cutoff
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (u : ℕ → X) (v : ℕ → ℕ → X) (err : ℕ → ℝ)
    (hErr : Tendsto err atTop (𝓝 0))
    (hApprox : ∀ k n, dist (u n) (v k n) ≤ err k)
    (hCutoff : ∀ k, CauchySeq (v k)) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  exact cauchySeq_tendsto_of_complete
    (v12_cauchy_of_uniform_cutoff u v err hErr hApprox hCutoff)

/-- Countable compact-product extraction: the subsequence precedes BOTH indices. -/
theorem v12_shared_cutoff_subsequence
    (X : ℕ → Type*) [∀ R, MetricSpace (X R)]
    (v : ∀ R, ℕ → ℕ → X R)
    (K : ∀ R, ℕ → Set (X R))
    (hK : ∀ R k, IsCompact (K R k))
    (hMem : ∀ R k n, v R k n ∈ K R k) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ R k, CauchySeq (fun n => v R k (σ n)) := by
  let w : ℕ → ((p : ℕ × ℕ) → X p.1) :=
    fun n p => v p.1 p.2 n
  have hProd : IsCompact
      {z : (p : ℕ × ℕ) → X p.1 | ∀ p, z p ∈ K p.1 p.2} :=
    isCompact_pi_infinite (fun p => hK p.1 p.2)
  have hw : ∀ n, w n ∈
      {z : (p : ℕ × ℕ) → X p.1 | ∀ p, z p ∈ K p.1 p.2} := by
    intro n p
    exact hMem p.1 p.2 n
  obtain ⟨z, _, σ, hσ, hlim⟩ := hProd.tendsto_subseq hw
  refine ⟨σ, hσ, ?_⟩
  intro R k
  have hc : Tendsto (fun n => v R k (σ n)) atTop (𝓝 (z (R, k))) := by
    simpa only [Function.comp_def, w] using
      ((continuous_apply (R, k)).tendsto z).comp hlim
  exact hc.cauchySeq

/-- A single subsequence converges in every member of a countable family. -/
theorem v12_countable_cutoff_limits
    (X : ℕ → Type*) [∀ R, MetricSpace (X R)] [∀ R, CompleteSpace (X R)]
    (u : ∀ R, ℕ → X R) (v : ∀ R, ℕ → ℕ → X R)
    (err : ℕ → ℝ) (hErr : Tendsto err atTop (𝓝 0))
    (hApprox : ∀ R k n, dist (u R n) (v R k n) ≤ err k)
    (K : ∀ R, ℕ → Set (X R))
    (hK : ∀ R k, IsCompact (K R k))
    (hMem : ∀ R k n, v R k n ∈ K R k) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ R, ∃ q : X R, Tendsto (fun n => u R (σ n)) atTop (𝓝 q) := by
  obtain ⟨σ, hσ, hCutoff⟩ := v12_shared_cutoff_subsequence X v K hK hMem
  refine ⟨σ, hσ, ?_⟩
  intro R
  exact v12_limit_of_uniform_cutoff
    (fun n => u R (σ n)) (fun k n => v R k (σ n)) err hErr
    (fun k n => hApprox R k (σ n)) (hCutoff R)

/-- Spatial R2, spacetime R x R2, and the two-component complex field. -/
abbrev V12Spatial := EuclideanSpace ℝ (Fin 2)
abbrev V12Spacetime := ℝ × V12Spatial
abbrev V12Field := EuclideanSpace ℂ (Fin 2)

/-- Product Lebesgue measure with time restricted to I=[a,b]. -/
noncomputable def v12_slab_measure (a b : ℝ) : Measure V12Spacetime :=
  ((volume : Measure ℝ).restrict (Set.Icc a b)).prod
    (volume : Measure V12Spatial)

/-- Integer-indexed spatial balls, radius R+1, exhausting R2. -/
def v12_spatial_cylinder (R : ℕ) : Set V12Spacetime :=
  {z | ‖z.2‖ < (R : ℝ) + 1}

/-- The spatial cylinder is exactly the full time axis times the open spatial ball. -/
theorem v12_spatial_cylinder_eq_prod_ball (R : ℕ) :
    v12_spatial_cylinder R =
      Set.univ ×ˢ Metric.ball (0 : V12Spatial) ((R : ℝ) + 1) := by
  ext z
  simp [v12_spatial_cylinder, Metric.mem_ball, dist_zero_right]

/-- The local cylinder measure splits into the finite time restriction and
the finite spatial-ball restriction. -/
theorem v12_cylinder_measure_eq_prod (a b : ℝ) (R : ℕ) :
    (v12_slab_measure a b).restrict (v12_spatial_cylinder R) =
      ((volume : Measure ℝ).restrict (Set.Icc a b)).prod
        ((volume : Measure V12Spatial).restrict
          (Metric.ball (0 : V12Spatial) ((R : ℝ) + 1))) := by
  rw [v12_slab_measure, v12_spatial_cylinder_eq_prod_ball]
  simpa using
    (Measure.prod_restrict
      (μ := (volume : Measure ℝ).restrict (Set.Icc a b))
      (ν := (volume : Measure V12Spatial))
      Set.univ (Metric.ball (0 : V12Spatial) ((R : ℝ) + 1))).symm

/-- Every local spacetime cylinder used by v12 has finite measure. -/
noncomputable instance v12_cylinder_isFiniteMeasure (a b : ℝ) (R : ℕ) :
    IsFiniteMeasure
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) := by
  haveI hspace :
      IsFiniteMeasure
        ((volume : Measure V12Spatial).restrict
          (Metric.ball (0 : V12Spatial) ((R : ℝ) + 1))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  rw [v12_cylinder_measure_eq_prod]
  infer_instance

/-- Explicit Type annotations take the carrier of Mathlib's Lp additive subgroup. -/
abbrev V12SlabL2 (a b : ℝ) : Type := Lp V12Field 2 (v12_slab_measure a b)
abbrev V12CylinderL2 (a b : ℝ) (R : ℕ) : Type :=
  Lp V12Field 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))

/-- The actual continuous linear restriction, not an unspecified norm symbol. -/
noncomputable def v12_localize (a b : ℝ) (R : ℕ) :
    V12SlabL2 a b →L[ℂ] V12CylinderL2 a b R :=
  LpToLpRestrictCLM V12Spacetime V12Field ℂ (v12_slab_measure a b) 2
    (v12_spatial_cylinder R)

theorem v12_localize_coeFn (a b : ℝ) (R : ℕ) (f : V12SlabL2 a b) :
    (v12_localize a b R f : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] f := by
  exact LpToLpRestrictCLM_coeFn ℂ (v12_spatial_cylinder R) f

theorem v12_localize_norm_le (a b : ℝ) (R : ℕ) (f : V12SlabL2 a b) :
    ‖v12_localize a b R f‖ ≤ ‖f‖ := by
  exact norm_Lp_toLp_restrict_le (v12_spatial_cylinder R) f

theorem v12_localize_dist_le (a b : ℝ) (R : ℕ) (f g : V12SlabL2 a b) :
    dist (v12_localize a b R f) (v12_localize a b R g) ≤ dist f g := by
  simpa only [dist_eq_norm, map_sub] using v12_localize_norm_le a b R (f - g)

/--
Concrete Bochner L2 bridge for v12:thm:tightness.

Inputs still to discharge for the PDE: P is now required to be an actual
continuous linear operator family on slab L2 and must be instantiated by the
manuscript's spatial Fourier cutoff. Q is the actual field as an Lp element;
hTail is its global tail bound and hCompact is fixed-cutoff local compactness
from the manuscript's space/time bounds.
No common subsequence and no target Cauchyness/convergence is an input.
-/
theorem v12_spacetime_L2_common_subsequence
    (a b : ℝ) (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (err : ℕ → ℝ) (hErr : Tendsto err atTop (𝓝 0))
    (hTail : ∀ k n, ‖Q n - P k (Q n)‖ ≤ err k)
    (hCompact : ∀ R k, IsCompact
      (closure (Set.range (fun n => v12_localize a b R (P k (Q n)))))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ R, ∃ q : V12CylinderL2 a b R,
        Tendsto (fun n => v12_localize a b R (Q (σ n))) atTop (𝓝 q) := by
  let u : ∀ R, ℕ → V12CylinderL2 a b R :=
    fun R n => v12_localize a b R (Q n)
  let v : ∀ R, ℕ → ℕ → V12CylinderL2 a b R :=
    fun R k n => v12_localize a b R (P k (Q n))
  let K : ∀ R, ℕ → Set (V12CylinderL2 a b R) :=
    fun R k => closure (Set.range (v R k))
  have hApprox : ∀ R k n, dist (u R n) (v R k n) ≤ err k := by
    intro R k n
    exact (v12_localize_dist_le a b R (Q n) (P k (Q n))).trans
      (by simpa only [dist_eq_norm] using hTail k n)
  have hK : ∀ R k, IsCompact (K R k) := hCompact
  have hMem : ∀ R k n, v R k n ∈ K R k := by
    intro R k n
    exact subset_closure (Set.mem_range_self n)
  exact v12_countable_cutoff_limits (V12CylinderL2 a b) u v err hErr
    hApprox K hK hMem

#print axioms v12_cauchy_of_uniform_cutoff
#print axioms v12_limit_of_uniform_cutoff
#print axioms v12_shared_cutoff_subsequence
#print axioms v12_countable_cutoff_limits
#print axioms v12_spatial_cylinder_eq_prod_ball
#print axioms v12_cylinder_measure_eq_prod
#print axioms v12_localize_coeFn
#print axioms v12_localize_norm_le
#print axioms v12_localize_dist_le
#print axioms v12_spacetime_L2_common_subsequence


/-! ===== merged from lean/v12/V12_FrequencyTailAdapter.lean ===== -/

open Filter
open scoped Topology

noncomputable def v12_tailSup
    (a b : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (k : ℕ) : ℝ :=
  sSup (Set.range (fun n => ‖Q n - P k (Q n)‖))

theorem v12_tail_range_bddAbove
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hQ : ∀ n, ‖Q n‖ ≤ M) :
    ∀ k, BddAbove (Set.range (fun n => ‖Q n - P k (Q n)‖)) := by
  intro k
  refine ⟨M + ‖P k‖ * M, ?_⟩
  rintro y ⟨n, rfl⟩
  have hmap : ‖P k (Q n)‖ ≤ ‖P k‖ * ‖Q n‖ :=
    ContinuousLinearMap.le_opNorm (P k) (Q n)
  have hmapM : ‖P k (Q n)‖ ≤ ‖P k‖ * M := by
    exact hmap.trans
      (mul_le_mul_of_nonneg_left (hQ n) (norm_nonneg (P k)))
  calc
    ‖Q n - P k (Q n)‖ ≤ ‖Q n‖ + ‖P k (Q n)‖ := norm_sub_le _ _
    _ ≤ M + ‖P k‖ * M := add_le_add (hQ n) hmapM

theorem v12_tail_le_tailSup
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hQ : ∀ n, ‖Q n‖ ≤ M) :
    ∀ k n, ‖Q n - P k (Q n)‖ ≤ v12_tailSup a b Q P k := by
  intro k n
  unfold v12_tailSup
  exact le_csSup
    (v12_tail_range_bddAbove a b M Q P hQ k)
    (Set.mem_range_self n)

theorem v12_manuscript_tail_adapter
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hQ : ∀ n, ‖Q n‖ ≤ M)
    (hFreqTight :
      Tendsto (fun k => v12_tailSup a b Q P k) atTop (𝓝 0)) :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0)
        ∧
      ∀ k n, ‖Q n - P k (Q n)‖ ≤ err k := by
  refine ⟨fun k => v12_tailSup a b Q P k, hFreqTight, ?_⟩
  exact v12_tail_le_tailSup a b M Q P hQ

#print axioms v12_tail_range_bddAbove
#print axioms v12_tail_le_tailSup
#print axioms v12_manuscript_tail_adapter


/-! ===== exact remaining local-limit compatibility boundary =====

The common-subsequence theorem above already uses actual Bochner L2 spaces
and actual restriction maps from the global slab to each cylinder.

The further identity between limits on nested cylinders is intentionally NOT
encoded here by transporting Lp values across propositionally equal restricted
measures.  That transport was the source of dependent-type noise in the
previous draft and is not needed for the extraction itself.

The next compactness/gluing batch will realize all local limits in one common
ambient representative space and prove nested compatibility there.  Until
then, compatibility/gluing remains an explicit open bridge; no theorem below
assumes it.
-/

/-! ===== exact remaining fixed-cutoff compactness boundary =====

For fixed cutoff and compact cylinder the manuscript obtains uniform spatial
smoothness and a common time Hölder modulus, then invokes Arzela--Ascoli.
Mathlib contains the exact Arzela--Ascoli theorem.  The concrete map from the
manuscript's fixed-frequency representatives into local Bochner L2 is the next
application bridge.  We do not hide that bridge behind a tautological wrapper.
-/

/-! ===== certified tail-to-common-subsequence assembly ===== -/

/--
This is the current exact endpoint of the certified tightness bridge.
The manuscript frequency-tail supremum and fixed-cutoff local compactness imply
ONE subsequence converging in every local Bochner L2 cylinder.

No local compatibility/gluing conclusion is included here; that is the next
explicit bridge.
-/
theorem v12_tightness_common_subsequence_from_tail
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hQ : ∀ n, ‖Q n‖ ≤ M)
    (hFreqTight :
      Tendsto (fun k => v12_tailSup a b Q P k) atTop (𝓝 0))
    (hCompact : ∀ R k, IsCompact
      (closure (Set.range (fun n => v12_localize a b R (P k (Q n)))))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ R, ∃ q : V12CylinderL2 a b R,
        Tendsto (fun n => v12_localize a b R (Q (σ n)))
          atTop (𝓝 q) := by
  obtain ⟨err, hErr, hTail⟩ :=
    v12_manuscript_tail_adapter a b M Q P hQ hFreqTight
  exact v12_spacetime_L2_common_subsequence
    a b Q P err hErr hTail hCompact

#print axioms v12_tightness_common_subsequence_from_tail

/-! ===== merged from lean/v12/V12_FiniteSlabEnergy.lean ===== -/

open MeasureTheory Filter
open scoped ENNReal Topology

/--
Finite-time L^∞_t L^2_x control implies membership in the product-space L^2.

The hypothesis hFiberBound is exactly the energy bound on almost every time
slice.  The proof is only Fubini/Tonelli plus integrability of a constant on a
finite measure space.
-/
theorem v12_memLp_two_of_fiber_energy
    {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure T) (ν : Measure X)
    [IsFiniteMeasure μ] [SFinite ν]
    (f : T × X → E)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (M : ℝ) (hM : 0 ≤ M)
    (hFiberIntegrable :
      ∀ᵐ t ∂μ, Integrable (fun x => ‖f (t, x)‖ ^ 2) ν)
    (hFiberBound :
      ∀ᵐ t ∂μ, (∫ x, ‖f (t, x)‖ ^ 2 ∂ν) ≤ M ^ 2) :
    MemLp f 2 (μ.prod ν) := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  let g : T × X → ℝ := fun z => ‖f z‖ ^ 2
  have hg : AEStronglyMeasurable g (μ.prod ν) := hf.norm.pow 2
  rw [integrable_prod_iff hg]
  refine ⟨hFiberIntegrable, ?_⟩
  have hOuterMeas :
      AEStronglyMeasurable
        (fun t => ∫ x, ‖g (t, x)‖ ∂ν) μ :=
    hg.norm.integral_prod_right'
  refine Integrable.mono'
    (integrable_const (M ^ 2)) hOuterMeas ?_
  filter_upwards [hFiberBound] with t ht
  have hnonneg :
      0 ≤ ∫ x, ‖g (t, x)‖ ∂ν :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => norm_nonneg (g (t, x)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    (∫ x, ‖g (t, x)‖ ∂ν)
        = ∫ x, ‖f (t, x)‖ ^ 2 ∂ν := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (t, x)‖)]
    _ ≤ M ^ 2 := ht

/-- The time-restricted Lebesgue measure used in the manuscript is finite. -/
noncomputable def v12_time_measure (a b : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Icc a b)

theorem v12_time_measure_finite (a b : ℝ) :
    IsFiniteMeasure (v12_time_measure a b) := by
  unfold v12_time_measure
  exact MeasureTheory.isFiniteMeasure_restrict.mpr
    (isCompact_Icc.measure_lt_top.ne)

#print axioms v12_memLp_two_of_fiber_energy
#print axioms v12_time_measure_finite


/-! ===== merged from lean/v12/V12_SpatialFourierCutoff.lean ===== -/

open MeasureTheory FourierTransform
open scoped ENNReal

abbrev V12SpatialL2 : Type := Lp (α := V12Spatial) V12Field 2
abbrev V12SymbolLInf : Type := Lp (α := V12Spatial) ℂ ∞

/--
Multiplication by a fixed L-infinity scalar symbol is a continuous linear map
on vector-valued spatial L2.
-/
noncomputable def v12_L2Multiplier (m : V12SymbolLInf) :
    V12SpatialL2 →L[ℂ] V12SpatialL2 := by
  let B : ℂ →L[ℂ] V12Field →L[ℂ] V12Field :=
    ContinuousLinearMap.lsmul ℂ ℂ
  exact (B.holderL (volume : Measure V12Spatial) ∞ 2 2) m

theorem v12_L2Multiplier_bound
    (m : V12SymbolLInf) (f : V12SpatialL2) :
    ‖v12_L2Multiplier m f‖ ≤ ‖m‖ * ‖f‖ := by
  let B : ℂ →L[ℂ] V12Field →L[ℂ] V12Field :=
    ContinuousLinearMap.lsmul ℂ ℂ
  have hholder :
      ‖(B.holderL (volume : Measure V12Spatial) ∞ 2 2) m f‖
        ≤ ‖B‖ * ‖m‖ * ‖f‖ :=
    B.norm_holder_apply_apply_le m f
  have hB : ‖B‖ ≤ 1 := by
    dsimp [B]
    exact ContinuousLinearMap.opNorm_lsmul_le
  change ‖(B.holderL (volume : Measure V12Spatial) ∞ 2 2) m f‖
      ≤ ‖m‖ * ‖f‖
  calc
    _ ≤ ‖B‖ * ‖m‖ * ‖f‖ := hholder
    _ ≤ 1 * ‖m‖ * ‖f‖ := by
      gcongr
    _ = ‖m‖ * ‖f‖ := by ring

/-- The actual L2 Fourier multiplier F^{-1} M_m F. -/
noncomputable def v12_spatialFourierMultiplier (m : V12SymbolLInf) :
    V12SpatialL2 →L[ℂ] V12SpatialL2 :=
  fourierInvCLM ℂ V12SpatialL2 ∘L
    v12_L2Multiplier m ∘L
      fourierCLM ℂ V12SpatialL2

@[simp]
theorem v12_spatialFourierMultiplier_apply
    (m : V12SymbolLInf) (f : V12SpatialL2) :
    v12_spatialFourierMultiplier m f =
      𝓕⁻ (v12_L2Multiplier m (𝓕 f)) := rfl

theorem v12_norm_fourierInv_eq (g : V12SpatialL2) :
    ‖𝓕⁻ g‖ = ‖g‖ := by
  exact (Lp.fourierTransformₗᵢ V12Spatial V12Field).symm.norm_map g

theorem v12_spatialFourierMultiplier_bound
    (m : V12SymbolLInf) (f : V12SpatialL2) :
    ‖v12_spatialFourierMultiplier m f‖ ≤ ‖m‖ * ‖f‖ := by
  rw [v12_spatialFourierMultiplier_apply, v12_norm_fourierInv_eq]
  calc
    ‖v12_L2Multiplier m (𝓕 f)‖
        ≤ ‖m‖ * ‖𝓕 f‖ := v12_L2Multiplier_bound m (𝓕 f)
    _ = ‖m‖ * ‖f‖ := by rw [Lp.norm_fourier_eq]

theorem v12_spatialFourierMultiplier_norm_le
    (m : V12SymbolLInf) :
    ‖v12_spatialFourierMultiplier m‖ ≤ ‖m‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m)
    (v12_spatialFourierMultiplier_bound m)

/--
A bounded continuous scalar symbol gives an actual L-infinity equivalence
class on spatial frequency space without any finite-measure hypothesis.
-/
noncomputable def v12_symbolToLInf
    (m : BoundedContinuousFunction V12Spatial ℂ) : V12SymbolLInf :=
  (BoundedContinuousFunction.memLp_top m).toLp m

theorem v12_symbolToLInf_ae
    (m : BoundedContinuousFunction V12Spatial ℂ) :
    (v12_symbolToLInf m : V12Spatial → ℂ) =ᵐ[volume] m := by
  exact MemLp.coeFn_toLp (BoundedContinuousFunction.memLp_top m)

#print axioms v12_L2Multiplier_bound
#print axioms v12_spatialFourierMultiplier
#print axioms v12_spatialFourierMultiplier_bound
#print axioms v12_spatialFourierMultiplier_norm_le
#print axioms v12_symbolToLInf_ae


/-! ===== actual L2 convolution continuous representative ===== -/

/-- Scalar spatial L2 kernel space. -/
abbrev V12ScalarL2 : Type := Lp (α := V12Spatial) ℂ 2

/-- The continuous family (x,y) ↦ x-y, curried in x. -/
noncomputable def v12_subLeftFamily :
    C(V12Spatial, C(V12Spatial, V12Spatial)) :=
  ContinuousMap.curry
    ⟨fun z : V12Spatial × V12Spatial => z.1 - z.2, by fun_prop⟩

@[simp]
theorem v12_subLeftFamily_apply (x y : V12Spatial) :
    v12_subLeftFamily x y = x - y := rfl

/-- Pull a scalar L2 kernel back by the measure-preserving map y ↦ x-y. -/
noncomputable def v12_reflectedTranslate
    (k : V12ScalarL2) (x : V12Spatial) : V12ScalarL2 :=
  Lp.compMeasurePreserving
    (v12_subLeftFamily x)
    ((volume : Measure V12Spatial).measurePreserving_sub_left x) k

theorem v12_reflectedTranslate_ae
    (k : V12ScalarL2) (x : V12Spatial) :
    (v12_reflectedTranslate k x : V12Spatial → ℂ)
      =ᵐ[(volume : Measure V12Spatial)] fun y => k (x - y) := by
  have hmp :
      MeasurePreserving (v12_subLeftFamily x)
        (volume : Measure V12Spatial) (volume : Measure V12Spatial) := by
    change MeasurePreserving (fun y : V12Spatial => x - y)
      (volume : Measure V12Spatial) (volume : Measure V12Spatial)
    exact (volume : Measure V12Spatial).measurePreserving_sub_left x
  have h :=
    Lp.coeFn_compMeasurePreserving k hmp
  simpa [v12_reflectedTranslate, Function.comp_def] using h

@[simp]
theorem v12_reflectedTranslate_norm
    (k : V12ScalarL2) (x : V12Spatial) :
    ‖v12_reflectedTranslate k x‖ = ‖k‖ := by
  have hmp :
      MeasurePreserving (v12_subLeftFamily x)
        (volume : Measure V12Spatial) (volume : Measure V12Spatial) := by
    change MeasurePreserving (fun y : V12Spatial => x - y)
      (volume : Measure V12Spatial) (volume : Measure V12Spatial)
    exact (volume : Measure V12Spatial).measurePreserving_sub_left x
  exact Lp.norm_compMeasurePreserving k hmp

/-- x ↦ k(x-·) is continuous as an L2-valued map. -/
theorem v12_continuous_reflectedTranslate (k : V12ScalarL2) :
    Continuous (v12_reflectedTranslate k) := by
  have hg : Continuous (fun x : V12Spatial => v12_subLeftFamily x) :=
    v12_subLeftFamily.continuous
  have hgm : ∀ x : V12Spatial,
      MeasurePreserving (v12_subLeftFamily x)
        (volume : Measure V12Spatial) (volume : Measure V12Spatial) := by
    intro x
    change MeasurePreserving (fun y : V12Spatial => x - y)
      (volume : Measure V12Spatial) (volume : Measure V12Spatial)
    exact (volume : Measure V12Spatial).measurePreserving_sub_left x
  change Continuous (fun x : V12Spatial =>
    Lp.compMeasurePreserving (v12_subLeftFamily x) (hgm x) k)
  exact
    Continuous.compMeasurePreservingLp
      (μ := (volume : Measure V12Spatial))
      (ν := (volume : Measure V12Spatial))
      (E := ℂ) (p := (2 : ℝ≥0∞))
      (f := fun _ : V12Spatial => k)
      (g := fun x : V12Spatial => v12_subLeftFamily x)
      continuous_const hg hgm (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

/-- The L2-L2 Hölder pairing implementing scalar-kernel convolution. -/
noncomputable def v12_L2ConvolutionPairing :
    V12ScalarL2 →L[ℂ] V12SpatialL2 →L[ℂ] V12Field :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := V12Field)).lpPairing
    (volume : Measure V12Spatial) 2 2

/-- Continuous pointwise representative of k*f. -/
noncomputable def v12_L2ConvolutionRep
    (k : V12ScalarL2) (f : V12SpatialL2) (x : V12Spatial) : V12Field :=
  v12_L2ConvolutionPairing (v12_reflectedTranslate k x) f

theorem v12_continuous_L2ConvolutionRep
    (k : V12ScalarL2) (f : V12SpatialL2) :
    Continuous (v12_L2ConvolutionRep k f) := by
  change Continuous (fun x : V12Spatial =>
    v12_L2ConvolutionPairing (v12_reflectedTranslate k x) f)
  exact
    v12_L2ConvolutionPairing.continuous₂.comp₂
      (v12_continuous_reflectedTranslate k) continuous_const

/-- The bundled pairing is exactly the usual convolution integral. -/
theorem v12_L2ConvolutionRep_eq_integral
    (k : V12ScalarL2) (f : V12SpatialL2) (x : V12Spatial) :
    v12_L2ConvolutionRep k f x =
      ∫ y : V12Spatial, k (x - y) • f y := by
  rw [v12_L2ConvolutionRep, v12_L2ConvolutionPairing,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [v12_reflectedTranslate_ae k x] with y hy
  rw [hy]
  rfl

/-- Uniform pointwise estimate at fixed kernel. -/
theorem v12_L2ConvolutionRep_norm_le
    (k : V12ScalarL2) (f : V12SpatialL2) (x : V12Spatial) :
    ‖v12_L2ConvolutionRep k f x‖ ≤
      ‖v12_L2ConvolutionPairing‖ * ‖k‖ * ‖f‖ := by
  calc
    ‖v12_L2ConvolutionRep k f x‖
        = ‖v12_L2ConvolutionPairing (v12_reflectedTranslate k x) f‖ := rfl
    _ ≤ ‖v12_L2ConvolutionPairing (v12_reflectedTranslate k x)‖ * ‖f‖ :=
      (v12_L2ConvolutionPairing (v12_reflectedTranslate k x)).le_opNorm f
    _ ≤ (‖v12_L2ConvolutionPairing‖ *
          ‖v12_reflectedTranslate k x‖) * ‖f‖ := by
      gcongr
      exact v12_L2ConvolutionPairing.le_opNorm (v12_reflectedTranslate k x)
    _ = ‖v12_L2ConvolutionPairing‖ * ‖k‖ * ‖f‖ := by
      rw [v12_reflectedTranslate_norm]

/-- Spatial differences reduce to the L2 translation modulus of the fixed kernel. -/
theorem v12_L2ConvolutionRep_dist_le
    (k : V12ScalarL2) (f : V12SpatialL2) (x y : V12Spatial) :
    dist (v12_L2ConvolutionRep k f x) (v12_L2ConvolutionRep k f y) ≤
      ‖v12_L2ConvolutionPairing‖ *
        dist (v12_reflectedTranslate k x) (v12_reflectedTranslate k y) * ‖f‖ := by
  rw [dist_eq_norm, v12_L2ConvolutionRep]
  have hmap :
      v12_L2ConvolutionPairing
          (v12_reflectedTranslate k x - v12_reflectedTranslate k y) =
        v12_L2ConvolutionPairing (v12_reflectedTranslate k x) -
          v12_L2ConvolutionPairing (v12_reflectedTranslate k y) :=
    map_sub v12_L2ConvolutionPairing _ _
  calc
    ‖v12_L2ConvolutionPairing (v12_reflectedTranslate k x) f -
        v12_L2ConvolutionPairing (v12_reflectedTranslate k y) f‖
        = ‖v12_L2ConvolutionPairing
            (v12_reflectedTranslate k x - v12_reflectedTranslate k y) f‖ := by
          rw [hmap]
          rfl
    _ ≤ ‖v12_L2ConvolutionPairing
          (v12_reflectedTranslate k x - v12_reflectedTranslate k y)‖ * ‖f‖ :=
      (v12_L2ConvolutionPairing
        (v12_reflectedTranslate k x - v12_reflectedTranslate k y)).le_opNorm f
    _ ≤
        (‖v12_L2ConvolutionPairing‖ *
          ‖v12_reflectedTranslate k x - v12_reflectedTranslate k y‖) * ‖f‖ := by
      gcongr
      exact v12_L2ConvolutionPairing.le_opNorm
        (v12_reflectedTranslate k x - v12_reflectedTranslate k y)
    _ = ‖v12_L2ConvolutionPairing‖ *
        dist (v12_reflectedTranslate k x) (v12_reflectedTranslate k y) * ‖f‖ := by
      rw [dist_eq_norm]

#print axioms v12_reflectedTranslate_ae
#print axioms v12_reflectedTranslate_norm
#print axioms v12_continuous_reflectedTranslate
#print axioms v12_continuous_L2ConvolutionRep
#print axioms v12_L2ConvolutionRep_eq_integral
#print axioms v12_L2ConvolutionRep_norm_le
#print axioms v12_L2ConvolutionRep_dist_le

/-! ===== merged from lean/v12/V12_EquicontinuityAdapter.lean ===== -/

open Filter
open scoped Topology

/--
A common continuity modulus gives the exact equicontinuity hypothesis needed
by Arzela--Ascoli.  This is Mathlib's metric equicontinuity theorem specialized
to a sequence.
-/
theorem v12_equicontinuous_of_common_modulus
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝 0) (𝓝 0))
    (hmod : ∀ x y n, dist (F n x) (F n y) ≤ ω (dist x y)) :
    Equicontinuous F := by
  exact Metric.equicontinuous_of_continuity_modulus ω hω F hmod

/--
A linear modulus is the special case used for the fixed-frequency spatial
Lipschitz estimate.
-/
theorem v12_equicontinuous_of_uniform_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (C : ℝ)
    (hmod : ∀ x y n, dist (F n x) (F n y) ≤ C * dist x y) :
    Equicontinuous F := by
  apply v12_equicontinuous_of_common_modulus F (fun r => C * r)
  · have hC : Tendsto (fun _ : ℝ => C) (𝓝 0) (𝓝 C) := tendsto_const_nhds
    have hid : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0) := tendsto_id
    simpa using hC.mul hid
  · exact hmod

/--
Two manuscript estimates may be combined before invoking Ascoli:
one term controls spatial motion and one controls time motion.  The theorem is
stated with an already assembled scalar modulus because the product-domain
metric realization is handled by the concrete representative map.
-/
theorem v12_equicontinuous_of_space_time_modulus
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y)
    (ωspace ωtime : ℝ → ℝ)
    (hspace : Tendsto ωspace (𝓝 0) (𝓝 0))
    (htime : Tendsto ωtime (𝓝 0) (𝓝 0))
    (hmod : ∀ x y n,
      dist (F n x) (F n y)
        ≤ ωspace (dist x y) + ωtime (dist x y)) :
    Equicontinuous F := by
  apply v12_equicontinuous_of_common_modulus F
    (fun r => ωspace r + ωtime r)
  · simpa using hspace.add htime
  · exact hmod

#print axioms v12_equicontinuous_of_common_modulus
#print axioms v12_equicontinuous_of_uniform_lipschitz
#print axioms v12_equicontinuous_of_space_time_modulus


/-! ===== compact-domain Arzela--Ascoli bridge ===== -/

/--
For a compact metric parameter domain, an equicontinuous uniformly bounded
sequence of V12Field-valued bounded continuous maps has compact closure in the
sup-norm topology.

This is the pinned Mathlib Arzela--Ascoli theorem directly, with the common
range compact set chosen to be a finite-dimensional closed ball.
-/
theorem v12_ascoli_compact_domain
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : ℕ → (BoundedContinuousFunction X V12Field))
    (M : ℝ)
    (hEq : Equicontinuous ((↑) : Set.range F → X → V12Field))
    (hBound : ∀ n x, ‖F n x‖ ≤ M) :
    IsCompact (closure (Set.range F)) := by
  apply BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : V12Field) M) (isCompact_closedBall 0 M)
    (Set.range F)
  · intro f x hf
    obtain ⟨n, rfl⟩ := hf
    simpa only [Metric.mem_closedBall, dist_zero_right] using hBound n x
  · exact hEq

/--
A continuous linear image of the Ascoli family is compact.
This is the generic bridge used after a fixed-frequency continuous
representative has been placed in a concrete local Bochner-L2 realization.
-/
theorem v12_ascoli_linear_image_compact
    {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : ℕ → (BoundedContinuousFunction X V12Field))
    (J : (BoundedContinuousFunction X V12Field) →L[ℂ] Y)
    (M : ℝ)
    (hEq : Equicontinuous ((↑) : Set.range F → X → V12Field))
    (hBound : ∀ n x, ‖F n x‖ ≤ M) :
    IsCompact (closure (Set.range (fun n => J (F n)))) := by
  have hC := v12_ascoli_compact_domain F M hEq hBound
  have hImage : IsCompact (J '' closure (Set.range F)) :=
    hC.image J.continuous
  have hsub :
      Set.range (fun n => J (F n))
        ⊆ J '' closure (Set.range F) := by
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨F n, subset_closure (Set.mem_range_self n), rfl⟩
  exact hImage.of_isClosed_subset isClosed_closure
    (closure_minimal hsub hImage.isClosed)


/-! ===== Ascoli representative to actual local-L2 bridge ===== -/

/--
If two local L2 classes admit representatives obtained by evaluating two bounded
continuous functions along the same parameter map, their L2 distance is bounded
by the sup-distance times the L2 norm of the constant one function.
No measurability or continuity of the parameter map is needed here: the actual
a.e. representative identities are supplied explicitly.
-/
theorem v12_localLp_dist_le_sup_of_ae_rep
    {X Ω : Type*} [MetricSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : Ω → X)
    (F G : BoundedContinuousFunction X V12Field)
    (u v : Lp V12Field 2 μ)
    (hu : (u : Ω → V12Field) =ᵐ[μ] fun z => F (r z))
    (hv : (v : Ω → V12Field) =ᵐ[μ] fun z => G (r z)) :
    dist u v ≤
      dist F G * ‖Lp.const (2 : ℝ≥0∞) μ (1 : ℝ)‖ := by
  rw [dist_eq_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
    (g := Lp.const (2 : ℝ≥0∞) μ (1 : ℝ))
  filter_upwards [Lp.coeFn_sub u v, hu, hv,
    Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := μ) (c := (1 : ℝ))] with z hsub huz hvz hone
  rw [hsub]
  simp only [Pi.sub_apply, huz, hvz, hone, Function.const_apply, norm_one, mul_one]
  simpa only [dist_eq_norm] using
    (BoundedContinuousFunction.dist_coe_le_dist (f := F) (g := G) (r z))

/--
A Cauchy sequence in the bounded-continuous sup norm transfers to a Cauchy
sequence of actual L2 classes whenever all terms have the stated common
representative map.
-/
theorem v12_cauchy_localLp_of_cauchy_bcf
    {X Ω : Type*} [MetricSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : Ω → X)
    (F : ℕ → BoundedContinuousFunction X V12Field)
    (u : ℕ → Lp V12Field 2 μ)
    (hF : CauchySeq F)
    (hRep : ∀ n, (u n : Ω → V12Field) =ᵐ[μ] fun z => F n (r z)) :
    CauchySeq u := by
  let C : ℝ := ‖Lp.const (2 : ℝ≥0∞) μ (1 : ℝ)‖
  have hC0 : 0 ≤ C := norm_nonneg _
  by_cases hC : C = 0
  · apply Metric.cauchySeq_iff.mpr
    intro ε hε
    refine ⟨0, ?_⟩
    intro m _ n _
    have hle := v12_localLp_dist_le_sup_of_ae_rep
      μ r (F m) (F n) (u m) (u n) (hRep m) (hRep n)
    have hle0 : dist (u m) (u n) ≤ 0 := by
      simpa [C, hC] using hle
    exact hle0.trans_lt hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hC)
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.mp hF (ε / C) (div_pos hε hCpos)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hle := v12_localLp_dist_le_sup_of_ae_rep
      μ r (F m) (F n) (u m) (u n) (hRep m) (hRep n)
    calc
      dist (u m) (u n) ≤ dist (F m) (F n) * C := by
        simpa [C] using hle
      _ < (ε / C) * C :=
        mul_lt_mul_of_pos_right (hN m hm n hn) hCpos
      _ = ε := div_mul_cancel₀ ε hC

/--
Ascoli compactness plus an actual a.e. representative identification yields a
strictly increasing subsequence that is Cauchy in the target local L2 space.
This is the precise abstract bridge needed before instantiating the manuscript
fixed-frequency PDE estimates.
-/
theorem v12_ascoli_localLp_subsequence
    {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : Ω → X)
    (F : ℕ → BoundedContinuousFunction X V12Field)
    (u : ℕ → Lp V12Field 2 μ)
    (M : ℝ)
    (hEq : Equicontinuous ((↑) : Set.range F → X → V12Field))
    (hBound : ∀ n x, ‖F n x‖ ≤ M)
    (hRep : ∀ n, (u n : Ω → V12Field) =ᵐ[μ] fun z => F n (r z)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      CauchySeq (fun n => u (σ n)) := by
  have hK := v12_ascoli_compact_domain F M hEq hBound
  have hMem : ∀ n, F n ∈ closure (Set.range F) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨Flim, _, σ, hσ, hlim⟩ := hK.tendsto_subseq hMem
  refine ⟨σ, hσ, ?_⟩
  have hFCauchy : CauchySeq (fun n => F (σ n)) := hlim.cauchySeq
  exact v12_cauchy_localLp_of_cauchy_bcf
    μ r (fun n => F (σ n)) (fun n => u (σ n))
    hFCauchy (fun n => hRep (σ n))



/--
Ascoli compactness and an a.e. representative identification imply compactness
of the closure of the actual L2 range.  The proof does not construct a
subtype-L2 equivalence: it transfers total boundedness through the quantitative
distance estimate and then uses completeness of L2.
-/
theorem v12_ascoli_localLp_compact
    {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : Ω → X)
    (F : ℕ → BoundedContinuousFunction X V12Field)
    (u : ℕ → Lp V12Field 2 μ)
    (M : ℝ)
    (hEq : Equicontinuous ((↑) : Set.range F → X → V12Field))
    (hBound : ∀ n x, ‖F n x‖ ≤ M)
    (hRep : ∀ n, (u n : Ω → V12Field) =ᵐ[μ] fun z => F n (r z)) :
    IsCompact (closure (Set.range u)) := by
  let S : Set (BoundedContinuousFunction X V12Field) := Set.range F
  have hKS : IsCompact (closure S) := by
    simpa [S] using v12_ascoli_compact_domain F M hEq hBound
  have hSTB : TotallyBounded S :=
    hKS.totallyBounded.subset subset_closure
  let idx : S → ℕ := fun f => Classical.choose f.property
  have hidx : ∀ f : S, F (idx f) = f.1 := by
    intro f
    exact Classical.choose_spec f.property
  let T : S → Lp V12Field 2 μ := fun f => u (idx f)
  let C : NNReal := ‖Lp.const (2 : ℝ≥0∞) μ (1 : ℝ)‖₊
  have hLip : LipschitzWith C T := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    have hle := v12_localLp_dist_le_sup_of_ae_rep
      μ r (F (idx f)) (F (idx g))
      (u (idx f)) (u (idx g))
      (hRep (idx f)) (hRep (idx g))
    calc
      dist (T f) (T g)
          = dist (u (idx f)) (u (idx g)) := rfl
      _ ≤ dist (F (idx f)) (F (idx g)) *
          ‖Lp.const (2 : ℝ≥0∞) μ (1 : ℝ)‖ := hle
      _ = (C : ℝ) * dist f g := by
        rw [hidx f, hidx g]
        change
          dist f.1 g.1 * ‖Lp.const (2 : ℝ≥0∞) μ (1 : ℝ)‖ =
            (C : ℝ) * dist f.1 g.1
        simp [C, mul_comm]
  have hSubTB : TotallyBounded (Set.univ : Set S) := by
    have hpre :
        TotallyBounded
          ((Subtype.val : S → BoundedContinuousFunction X V12Field) ⁻¹' S) :=
      totallyBounded_preimage
        (f := (Subtype.val : S → BoundedContinuousFunction X V12Field))
        (s := S)
        isUniformEmbedding_subtype_val.isUniformInducing hSTB
    have hpre_eq :
        ((Subtype.val : S → BoundedContinuousFunction X V12Field) ⁻¹' S)
          = (Set.univ : Set S) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact f.2
    rwa [hpre_eq] at hpre
  have hImageTB : TotallyBounded (T '' (Set.univ : Set S)) :=
    hSubTB.image hLip.uniformContinuous
  have hRangeSub : Set.range u ⊆ T '' (Set.univ : Set S) := by
    rintro y ⟨n, rfl⟩
    let f : S := ⟨F n, Set.mem_range_self n⟩
    have hfidx : F (idx f) = F n := by
      simpa [f] using hidx f
    have huEq : u (idx f) = u n := by
      apply eq_of_dist_eq_zero
      have hle := v12_localLp_dist_le_sup_of_ae_rep
        μ r (F (idx f)) (F n)
        (u (idx f)) (u n)
        (hRep (idx f)) (hRep n)
      apply le_antisymm
      · exact hle.trans_eq (by rw [hfidx, dist_self, zero_mul])
      · exact dist_nonneg
    refine ⟨f, Set.mem_univ f, ?_⟩
    simpa [T] using huEq
  have hRangeTB : TotallyBounded (Set.range u) :=
    TotallyBounded.subset hRangeSub hImageTB
  exact hRangeTB.closure.isCompact_of_isClosed isClosed_closure


/-! ===== V12 compact-cylinder representative bridge ===== -/

/-- The closed compact cylinder used for Arzela--Ascoli.  The time interval is
written with min/max so the type remains nonempty even for formal inputs a > b. -/
def v12_closed_spacetime_cylinder (a b : ℝ) (R : ℕ) : Set V12Spacetime :=
  Set.Icc (min a b) (max a b) ×ˢ
    Metric.closedBall (0 : V12Spatial) ((R : ℝ) + 1)

/-- The compact cylinder as an actual type. -/
abbrev V12CompactCylinder (a b : ℝ) (R : ℕ) : Type :=
  v12_closed_spacetime_cylinder a b R

noncomputable instance v12_compactCylinder_compactSpace (a b : ℝ) (R : ℕ) :
    CompactSpace (V12CompactCylinder a b R) :=
  isCompact_iff_compactSpace.mp <|
    IsCompact.prod isCompact_Icc
      (isCompact_closedBall (0 : V12Spatial) ((R : ℝ) + 1))

/-- The local cylinder measure is the ambient product Lebesgue measure
restricted to the open spacetime rectangle Icc(a,b) x ball(0,R+1). -/
theorem v12_cylinder_measure_eq_restrict_rect (a b : ℝ) (R : ℕ) :
    (v12_slab_measure a b).restrict (v12_spatial_cylinder R) =
      ((volume : Measure ℝ).prod (volume : Measure V12Spatial)).restrict
        (Set.Icc a b ×ˢ Metric.ball (0 : V12Spatial) ((R : ℝ) + 1)) := by
  rw [v12_cylinder_measure_eq_prod]
  exact Measure.prod_restrict
    (μ := (volume : Measure ℝ))
    (ν := (volume : Measure V12Spatial))
    (Set.Icc a b) (Metric.ball (0 : V12Spatial) ((R : ℝ) + 1))

/-- The local measure is almost everywhere supported in the closed compact
cylinder used by Ascoli. -/
theorem v12_local_measure_mem_closed_cylinder_ae (a b : ℝ) (R : ℕ) :
    ∀ᵐ z ∂((v12_slab_measure a b).restrict (v12_spatial_cylinder R)),
      z ∈ v12_closed_spacetime_cylinder a b R := by
  rw [v12_cylinder_measure_eq_restrict_rect]
  filter_upwards [
    self_mem_ae_restrict
      ((measurableSet_Icc.prod
        (measurableSet_ball :
          MeasurableSet (Metric.ball (0 : V12Spatial) ((R : ℝ) + 1)))))
  ] with z hz
  exact ⟨
    ⟨(min_le_left a b).trans hz.1.1,
      hz.1.2.trans (le_max_right a b)⟩,
    Metric.ball_subset_closedBall hz.2⟩

/-- A fixed base point of every closed compact cylinder. -/
noncomputable def v12_compactCylinderBase (a b : ℝ) (R : ℕ) :
    V12CompactCylinder a b R :=
  ⟨(min a b, 0), by
    constructor
    · exact ⟨le_rfl, min_le_max⟩
    · have hR : (0 : ℝ) ≤ (R : ℝ) + 1 := by positivity
      simpa only [Metric.mem_closedBall, dist_self] using hR⟩

/-- Send an arbitrary ambient spacetime point to the compact cylinder, using
the point itself on the closed cylinder and a fixed base point otherwise.
Continuity is not required: this map is used only under the restricted local
measure, where it is almost everywhere the identity. -/
noncomputable def v12_toCompactCylinder (a b : ℝ) (R : ℕ)
    (z : V12Spacetime) : V12CompactCylinder a b R := by
  classical
  exact if hz : z ∈ v12_closed_spacetime_cylinder a b R then ⟨z, hz⟩
    else v12_compactCylinderBase a b R

theorem v12_toCompactCylinder_coe_of_mem (a b : ℝ) (R : ℕ)
    {z : V12Spacetime} (hz : z ∈ v12_closed_spacetime_cylinder a b R) :
    ((v12_toCompactCylinder a b R z : V12CompactCylinder a b R) :
      V12Spacetime) = z := by
  classical
  simp [v12_toCompactCylinder, hz]

theorem v12_toCompactCylinder_coe_ae (a b : ℝ) (R : ℕ) :
    ∀ᵐ z ∂((v12_slab_measure a b).restrict (v12_spatial_cylinder R)),
      ((v12_toCompactCylinder a b R z : V12CompactCylinder a b R) :
        V12Spacetime) = z := by
  filter_upwards [v12_local_measure_mem_closed_cylinder_ae a b R] with z hz
  exact v12_toCompactCylinder_coe_of_mem a b R hz

/-- Restrict an ambient continuous representative to the compact cylinder and
bundle it with the sup norm. -/
noncomputable def v12_compactBCF (a b : ℝ) (R : ℕ)
    (g : C(V12Spacetime, V12Field)) :
    BoundedContinuousFunction (V12CompactCylinder a b R) V12Field :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => g z.1, g.continuous.comp continuous_subtype_val⟩

@[simp]
theorem v12_compactBCF_apply (a b : ℝ) (R : ℕ)
    (g : C(V12Spacetime, V12Field)) (z : V12CompactCylinder a b R) :
    v12_compactBCF a b R g z = g z.1 :=
  rfl

/-- An actual local L2 class represented by an ambient continuous function is
also represented almost everywhere by its compact-cylinder restriction after
the support map. -/
theorem v12_compactBCF_rep_ae (a b : ℝ) (R : ℕ)
    (g : C(V12Spacetime, V12Field))
    (u : V12CylinderL2 a b R)
    (hu :
      (u : V12Spacetime → V12Field)
        =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] g) :
    (u : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)]
        fun z => v12_compactBCF a b R g (v12_toCompactCylinder a b R z) := by
  filter_upwards [hu, v12_toCompactCylinder_coe_ae a b R] with z huz hcz
  rw [huz, v12_compactBCF_apply, hcz]

/-- V12-specialized Ascoli-to-local-L2 compactness: once the actual localized
cutoff classes possess ambient continuous representatives with uniform compact-
cylinder bounds and equicontinuity, their L2 closure is compact. -/
theorem v12_local_compact_of_continuous_representatives
    (a b : ℝ) (R : ℕ)
    (g : ℕ → C(V12Spacetime, V12Field))
    (u : ℕ → V12CylinderL2 a b R)
    (M : ℝ)
    (hEq :
      Equicontinuous
        ((↑) :
          Set.range (fun n => v12_compactBCF a b R (g n)) →
            V12CompactCylinder a b R → V12Field))
    (hBound :
      ∀ n z, ‖v12_compactBCF a b R (g n) z‖ ≤ M)
    (hRep :
      ∀ n,
        (u n : V12Spacetime → V12Field)
          =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] g n) :
    IsCompact (closure (Set.range u)) := by
  apply v12_ascoli_localLp_compact
    ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))
    (v12_toCompactCylinder a b R)
    (fun n => v12_compactBCF a b R (g n)) u M hEq hBound
  intro n
  exact v12_compactBCF_rep_ae a b R (g n) (u n) (hRep n)

#print axioms v12_cylinder_measure_eq_restrict_rect
#print axioms v12_local_measure_mem_closed_cylinder_ae
#print axioms v12_toCompactCylinder_coe_ae
#print axioms v12_compactBCF_rep_ae
#print axioms v12_local_compact_of_continuous_representatives

#print axioms v12_ascoli_compact_domain
#print axioms v12_ascoli_linear_image_compact
#print axioms v12_localLp_dist_le_sup_of_ae_rep
#print axioms v12_cauchy_localLp_of_cauchy_bcf
#print axioms v12_ascoli_localLp_subsequence
#print axioms v12_ascoli_localLp_compact

end SMScattering.W20Full
