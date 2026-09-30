import lean.v12.V12_YNonlinearLocalProducts

/-!
The weak-strong term in Theorem7.1. Uniform L2 bounds and weak L2 convergence
are explicit at this lemma; deriving them for the reconstructed V,W fields
remains a separate obligation. The varying-test error is proved here.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

section Bilinear
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem v12_bounded_fixed_test_strong_pairing_limit
    (B : E →L[ℂ] F →L[ℂ] G)
    (xn : ℕ → E) (yn : ℕ → F) (x : E) (y : F)
    (C : ℝ) (hC : ∀ n, ‖xn n‖ ≤ C)
    (hy : Tendsto yn atTop (𝓝 y))
    (hfixed : Tendsto (fun n => B (xn n) y) atTop (𝓝 (B x y))) :
    Tendsto (fun n => B (xn n) (yn n)) atTop (𝓝 (B x y)) := by
  have hn : Tendsto (fun n => ‖yn n - y‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hy.sub_const y).norm
  have hb : Tendsto (fun n => ‖B‖ * C * ‖yn n - y‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hn.const_mul (‖B‖ * C)
  have he : Tendsto (fun n => B (xn n) (yn n - y)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hb
    intro n
    apply (B.le_opNorm₂ (xn n) (yn n - y)).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg B)) (norm_nonneg _)
  have hh := he.add hfixed
  simpa only [map_sub, sub_add_cancel, zero_add] using hh
end Bilinear

/-- The actual complex integral, with a varying L2 test and weakly
convergent scalar L2 coefficient. No integral-limit premise for varying tests. -/
theorem v12_weak_L2_strong_L2_integral_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Vn : ℕ → Lp ℂ 2 μ) (V : Lp ℂ 2 μ)
    (qn : ℕ → Lp ℂ 2 μ) (q : Lp ℂ 2 μ)
    (C : ℝ) (hC : ∀ n, ‖Vn n‖ ≤ C)
    (hweak : ∀ φ : Lp ℂ 2 μ,
      Tendsto (fun n => ∫ z, Vn n z * φ z ∂μ) atTop (𝓝 (∫ z, V z * φ z ∂μ)))
    (hq : Tendsto qn atTop (𝓝 q)) :
    Tendsto (fun n => ∫ z, Vn n z * qn n z ∂μ) atTop (𝓝 (∫ z, V z * q z ∂μ)) := by
  let B := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  have hfixed : Tendsto (fun n => B (Vn n) q) atTop (𝓝 (B V q)) := by
    simpa only [B, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.mul_apply'] using hweak q
  have h := v12_bounded_fixed_test_strong_pairing_limit B Vn qn V q C hC hq hfixed
  simpa only [B, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply'] using h

#print axioms v12_bounded_fixed_test_strong_pairing_limit
#print axioms v12_weak_L2_strong_L2_integral_limit
end SMScattering.W20Full
