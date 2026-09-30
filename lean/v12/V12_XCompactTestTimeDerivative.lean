import lean.v12.V12_TestCutoffApproximation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
Differentiate the ACTUAL compact spatial test curve from a smooth raw field.
The parameter interval is open; no extension of the solution outside its
lifespan and no Banach-valued derivative of the full cutoff field is assumed.
The derivative domination is proved on a compact time-support product.
The raw partial derivative and its local continuity are explicit analytic
inputs, to be supplied by the smooth solution. No PDE residual is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal ContDiff

/-- A compact spatial test converts the pointwise time derivative of the
raw field into the derivative of its actual Bochner integral. -/
theorem v12_compact_pairing_hasDerivAt
    (J : Set ℝ) (hJ : IsOpen J)
    (ψ : V12Spatial → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (Q DQ : ℝ → V12Spatial → V12Field)
    (hQ : ∀ t ∈ J, Continuous (Q t))
    (hDQ : ContinuousOn (Function.uncurry DQ) (J ×ˢ Set.univ))
    (hder : ∀ t ∈ J, ∀ y, HasDerivAt (fun s => Q s y) (DQ t y) t)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => ∫ y : V12Spatial, ψ y • Q s y)
      (∫ y : V12Spatial, ψ y • DQ t y) t := by
  obtain ⟨ε, hε, hεJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds ht)
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := by linarith
  have hclosed : Metric.closedBall t (ε / 2) ⊆ J := by
    intro s hs
    exact hεJ (Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hs).trans_lt hrε))
  have hopen : Metric.ball t (ε / 2) ⊆ J :=
    fun s hs => hclosed (Metric.ball_subset_closedBall hs)
  have hK : IsCompact (Metric.closedBall t (ε / 2) ×ˢ tsupport ψ) :=
    (isCompact_closedBall t (ε / 2)).prod hc
  have hKsub : Metric.closedBall t (ε / 2) ×ˢ tsupport ψ ⊆ J ×ˢ Set.univ := by
    intro z hz
    exact ⟨hclosed hz.1, Set.mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hDQ.mono hKsub)
  have hDt : Continuous (fun y : V12Spatial => DQ t y) := by
    have hmap : Set.MapsTo (fun y : V12Spatial => (t, y)) Set.univ (J ×ˢ Set.univ) :=
      fun y _ => ⟨ht, Set.mem_univ y⟩
    have hcont := hDQ.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
    simpa only [continuousOn_univ, Function.comp_def] using hcont
  have hpsiint : Integrable ψ (volume : Measure V12Spatial) :=
    hψ.integrable_of_hasCompactSupport hc
  have hint : Integrable (fun y : V12Spatial => ψ y • Q t y) volume :=
    (hψ.smul (hQ t ht)).integrable_of_hasCompactSupport hc.smul_right
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun y : V12Spatial => ψ y • Q s y) volume := by
    filter_upwards [Metric.ball_mem_nhds t hr] with s hs
    exact (hψ.smul (hQ s (hopen hs))).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂(volume : Measure V12Spatial),
      ∀ s ∈ Metric.ball t (ε / 2), ‖ψ y • DQ s y‖ ≤ ‖ψ y‖ * C := by
    apply Filter.Eventually.of_forall
    intro y s hs
    by_cases hy : ψ y = 0
    · simp only [hy, zero_smul, norm_zero, zero_mul, le_refl]
    · have hyK : y ∈ tsupport ψ := subset_closure hy
      have hCy : ‖DQ s y‖ ≤ C :=
        hC (s, y) ⟨Metric.ball_subset_closedBall hs, hyK⟩
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left hCy (norm_nonneg _)
  have hdiff : ∀ᵐ y ∂(volume : Measure V12Spatial),
      ∀ s ∈ Metric.ball t (ε / 2),
        HasDerivAt (fun τ => ψ y • Q τ y) (ψ y • DQ s y) s :=
    Filter.Eventually.of_forall
      (fun y s hs => (hder s (hopen hs) y).const_smul (ψ y))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure V12Spatial))
    (F := fun s y => ψ y • Q s y) (F' := fun s y => ψ y • DQ s y)
    (bound := fun y => ‖ψ y‖ * C)
    (Metric.ball_mem_nhds t hr) hmeas hint
    (hψ.smul hDt).aestronglyMeasurable hbound
    (hpsiint.norm.mul_const C) hdiff).2

/-- The previous result applied to the same chi(y/(R+1)) K(x-y) family.
No derivative identity for the compact-test integral is an input. -/
theorem v12_actual_compact_test_time_derivative
    (J : Set ℝ) (hJ : IsOpen J)
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x : V12Spatial)
    (Q DQ : ℝ → V12Spatial → V12Field)
    (hQ : ∀ t ∈ J, Continuous (Q t))
    (hDQ : ContinuousOn (Function.uncurry DQ) (J ×ˢ Set.univ))
    (hder : ∀ t ∈ J, ∀ y, HasDerivAt (fun s => Q s y) (DQ t y) t)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => ∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • Q s y)
      (∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • DQ t y) t :=
  v12_compact_pairing_hasDerivAt J hJ (v12_compactSpatialTest χ k R x)
    (v12_compactSpatialTest_smooth χ hs k R x).continuous
    (v12_compactSpatialTest_compactSupport χ hc k R x) Q DQ hQ hDQ hder ht

#print axioms v12_compact_pairing_hasDerivAt
#print axioms v12_actual_compact_test_time_derivative

end SMScattering.W20Full
