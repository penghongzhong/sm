import lean.v12.V12_FrequencyTightnessLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
Concrete spatial tests for the W20 weak-time argument.
The scale is R+1, so every natural index gives a positive truncation radius.
The test is chi(y/(R+1)) K(x-y), not an arbitrary approximating family.
This module proves its smooth compact support, finite-Lp zero-order kernel
errors and actual endpoint integral convergence. It does not assume these
limits, identify a PDE residual, or assert convergence uniform in all x.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal ContDiff

noncomputable def v12_testScale (R : ℕ) : ℝ := 1 / ((R : ℝ) + 1)

theorem v12_testScale_pos (R : ℕ) : 0 < v12_testScale R := by
  unfold v12_testScale
  positivity

theorem v12_testScale_tendsto :
    Tendsto v12_testScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def v12_testScaleEquiv (R : ℕ) :
    V12Spatial ≃L[ℝ] V12Spatial :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (v12_testScale R) (ne_of_gt (v12_testScale_pos R)))

noncomputable def v12_testCutoff (χ : V12Spatial → ℝ) (R : ℕ)
    (y : V12Spatial) : ℝ := χ (v12_testScale R • y)

theorem v12_testCutoff_continuous (χ : V12Spatial → ℝ)
    (hχ : Continuous χ) (R : ℕ) : Continuous (v12_testCutoff χ R) := by
  unfold v12_testCutoff
  exact hχ.comp (show Continuous (fun y : V12Spatial => v12_testScale R • y) by fun_prop)

theorem v12_testCutoff_tendsto (χ : V12Spatial → ℝ)
    (hχ : Continuous χ) (hχ0 : χ 0 = 1) (y : V12Spatial) :
    Tendsto (fun R => v12_testCutoff χ R y) atTop (𝓝 1) := by
  have hy : Tendsto (fun R => v12_testScale R • y) atTop (𝓝 (0 : V12Spatial)) := by
    simpa only [zero_smul] using v12_testScale_tendsto.smul_const y
  simpa only [v12_testCutoff, hχ0, Function.comp_def] using (hχ.tendsto 0).comp hy

theorem v12_testCutoff_compactSupport (χ : V12Spatial → ℝ)
    (hχ : HasCompactSupport χ) (R : ℕ) :
    HasCompactSupport (v12_testCutoff χ R) := by
  exact hχ.comp_homeomorph (v12_testScaleEquiv R).toHomeomorph

theorem v12_testCutoff_smooth (χ : V12Spatial → ℝ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (R : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v12_testCutoff χ R) := by
  unfold v12_testCutoff
  exact hχ.comp (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun y : V12Spatial => v12_testScale R • y) by fun_prop)

noncomputable def v12_compactSpatialTest (χ : V12Spatial → ℝ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x y : V12Spatial) : ℂ :=
  v12_testCutoff χ R y • k (x - y)

theorem v12_compactSpatialTest_compactSupport (χ : V12Spatial → ℝ)
    (hχ : HasCompactSupport χ) (k : SchwartzMap V12Spatial ℂ)
    (R : ℕ) (x : V12Spatial) :
    HasCompactSupport (v12_compactSpatialTest χ k R x) := by
  exact (v12_testCutoff_compactSupport χ hχ R).smul_right

theorem v12_compactSpatialTest_smooth (χ : V12Spatial → ℝ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x : V12Spatial) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v12_compactSpatialTest χ k R x) := by
  unfold v12_compactSpatialTest
  have hk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : V12Spatial => k (x - y)) :=
    (k.smooth (⊤ : ℕ∞)).comp
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : V12Spatial => x - y) by fun_prop)
  exact (v12_testCutoff_smooth χ hχ R).smul hk

theorem v12_testCutoff_error_norm_le_one (χ : V12Spatial → ℝ)
    (hχ : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (R : ℕ) (y : V12Spatial) :
    ‖v12_testCutoff χ R y - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  obtain ⟨h0, h1⟩ := hχ (v12_testScale R • y)
  change |χ (v12_testScale R • y) - 1| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Dominated convergence for the actual dilated multiplier and any finite
nonzero exponent. In the manuscript this is applied only at p=2 and p=4. -/
theorem v12_testCutoff_error_eLpNorm_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure V12Spatial) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (χ : V12Spatial → ℝ) (hχc : Continuous χ) (hχ0 : χ 0 = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (f : V12Spatial → E) (hf : MemLp f p μ) :
    Tendsto (fun R => eLpNorm
      (fun y => (v12_testCutoff χ R y - 1) • f y) p μ) atTop (𝓝 0) := by
  let F : ℕ → V12Spatial → E :=
    fun R y => (v12_testCutoff χ R y - 1) • f y
  have hmeas : ∀ R, AEStronglyMeasurable (F R) μ := by
    intro R
    exact ((v12_testCutoff_continuous χ hχc R).sub continuous_const).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  have hdom : ∀ R y, ‖F R y‖ ≤ ‖f y‖ := by
    intro R y
    change ‖(v12_testCutoff χ R y - 1) • f y‖ ≤ ‖f y‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right
      (v12_testCutoff_error_norm_le_one χ hχb R y) (norm_nonneg _)).trans_eq (one_mul _)
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpowlim : Tendsto
      (fun R => ∫⁻ y, ‖F R y‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (fun y => ‖f y‖ₑ ^ p.toReal)
      (fun R => (hmeas R).enorm.pow_const p.toReal)
      (fun R => Filter.Eventually.of_forall (fun y => by
        apply ENNReal.rpow_le_rpow _ hp.le
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hdom R y)))
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt hf).ne
      (Filter.Eventually.of_forall (fun y => by
        have hF : Tendsto (fun R => F R y) atTop (𝓝 (0 : E)) := by
          simpa [F] using ((v12_testCutoff_tendsto χ hχc hχ0 y).sub_const 1).smul_const (f y)
        have he := continuous_enorm.continuousAt.tendsto.comp hF
        have hr := (show Continuous (fun z : ℝ≥0∞ => z ^ p.toReal) from
          ENNReal.continuous_rpow_const).continuousAt.tendsto.comp he
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp] using hr))
    simpa only [lintegral_zero] using h
  have hroot := (show Continuous (fun z : ℝ≥0∞ => z ^ (1 / p.toReal)) from
    ENNReal.continuous_rpow_const).continuousAt.tendsto.comp hpowlim
  have hroot' : Tendsto
      (fun R => (∫⁻ y, ‖F R y‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using hroot
  convert hroot' using 1
  ext R
  exact (eLpNorm_eq_eLpNorm' hp0 hpt (hmeas R)).trans
    (eLpNorm'_eq_lintegral_enorm _ _ _)

/-- The zero-order test error for the same Schwartz kernel at fixed x.
No tail estimate or convergence hypothesis occurs in the assumptions. -/
theorem v12_compactSpatialTest_error_tendsto
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (χ : V12Spatial → ℝ) (hχc : Continuous χ) (hχ0 : χ 0 = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial) :
    Tendsto (fun R => eLpNorm
      (fun y => v12_compactSpatialTest χ k R x y - k (x-y)) p volume)
        atTop (𝓝 0) := by
  have hk : MemLp (fun y => k (x-y)) p volume :=
    (k.memLp p volume).comp_measurePreserving (v12_subLeft_measurePreserving x)
  have h := v12_testCutoff_error_eLpNorm_tendsto volume p hp0 hpt
    χ hχc hχ0 hχb (fun y => k (x-y)) hk
  simpa only [v12_compactSpatialTest, sub_smul, one_smul] using h

/-- Actual cutoff integrals converge, with an integrable majorant.
This is used with H(y)=K(x-y) Q(t,y), whose integrability is proved below. -/
theorem v12_testCutoff_integral_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure V12Spatial)
    (χ : V12Spatial → ℝ) (hχc : Continuous χ) (hχ0 : χ 0 = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (H : V12Spatial → E) (hH : Integrable H μ) :
    Tendsto (fun R => ∫ y, v12_testCutoff χ R y • H y ∂μ) atTop
      (𝓝 (∫ y, H y ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => ‖H y‖)
  · intro R
    exact (v12_testCutoff_continuous χ hχc R).aestronglyMeasurable.smul hH.aestronglyMeasurable
  · exact hH.norm
  · intro R
    apply Filter.Eventually.of_forall
    intro y
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := hχb (v12_testScale R • y)
    change |χ (v12_testScale R • y)| * ‖H y‖ ≤ ‖H y‖
    rw [abs_of_nonneg h0]
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans_eq (one_mul _)
  · apply Filter.Eventually.of_forall
    intro y
    simpa only [one_smul] using (v12_testCutoff_tendsto χ hχc hχ0 y).smul_const (H y)

/-- Actual compact-test endpoint limit for an arbitrary spatial L2 input.
No convergence or integrability of the product is an input hypothesis. -/
theorem v12_compactSpatialTest_endpoint_tendsto
    (χ : V12Spatial → ℝ) (hχc : Continuous χ) (hχ0 : χ 0 = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial)
    (f : V12Spatial → V12Field) (hf : MemLp f 2 volume) :
    Tendsto (fun R => ∫ y, v12_compactSpatialTest χ k R x y • f y)
      atTop (𝓝 (∫ y, k (x-y) • f y)) := by
  have hk : MemLp (fun y => k (x-y)) 2 volume :=
    (k.memLp 2 volume).comp_measurePreserving (v12_subLeft_measurePreserving x)
  have hprod : Integrable (fun y => k (x-y) • f y) volume := by
    exact memLp_one_iff_integrable.mp
      ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] V12Field →L[ℂ] V12Field).memLp_of_bilin 1 hk hf)
  simpa only [v12_compactSpatialTest, smul_assoc] using
    v12_testCutoff_integral_tendsto volume χ hχc hχ0 hχb
      (fun y => k (x-y) • f y) hprod

#print axioms v12_testScale_tendsto
#print axioms v12_testCutoff_tendsto
#print axioms v12_compactSpatialTest_compactSupport
#print axioms v12_compactSpatialTest_smooth
#print axioms v12_testCutoff_error_eLpNorm_tendsto
#print axioms v12_compactSpatialTest_error_tendsto
#print axioms v12_testCutoff_integral_tendsto
#print axioms v12_compactSpatialTest_endpoint_tendsto

end SMScattering.W20Full
