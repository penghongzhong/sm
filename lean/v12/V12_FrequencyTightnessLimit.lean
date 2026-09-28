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

abbrev V12SlabL2 (a b : ℝ) := Lp V12Field 2 (v12_slab_measure a b)
abbrev V12CylinderL2 (a b : ℝ) (R : ℕ) :=
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

Inputs still to discharge for the PDE: P is the concrete spatial Fourier
cutoff, Q is the actual field as an Lp element, hTail is its global tail
bound, and hCompact is fixed-cutoff local compactness from space/time bounds.
No common subsequence and no target Cauchyness/convergence is an input.
-/
theorem v12_spacetime_L2_common_subsequence
    (a b : ℝ) (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b → V12SlabL2 a b)
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
#print axioms v12_localize_coeFn
#print axioms v12_localize_norm_le
#print axioms v12_localize_dist_le
#print axioms v12_spacetime_L2_common_subsequence

end SMScattering.W20Full
