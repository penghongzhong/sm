import lean.v12.V12_TestDerivatives

/-!
Finite-Lp derivative errors of the exact compact spatial test.
The derivative identities are proved in V12_TestDerivatives. Here dominated
convergence controls the cutoff-derivative terms and reflected kernel tails.
The conclusion includes p=2; p=infinity is expressly excluded.
Limits are for fixed x, not uniform over all spatial translations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory LineDeriv
open scoped Topology ENNReal ContDiff

/-- A finite-Lp dominated convergence leaf with no convergence-in-norm input. -/
theorem v12_dominated_eLpNorm_tendsto_zero
    {E : Type*} [NormedAddCommGroup E]
    (μ : Measure V12Spatial) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (F : ℕ → V12Spatial → E) (g : V12Spatial → ℝ)
    (hg : MemLp g p μ)
    (hmeas : ∀ R, AEStronglyMeasurable (F R) μ)
    (hdom : ∀ R y, ‖F R y‖ ≤ ‖g y‖)
    (hpoint : ∀ y, Tendsto (fun R => F R y) atTop (𝓝 0)) :
    Tendsto (fun R => eLpNorm (F R) p μ) atTop (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpowlim : Tendsto
      (fun R => ∫⁻ y, ‖F R y‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (fun y => ‖g y‖ₑ ^ p.toReal)
      (fun R => (hmeas R).enorm.pow_const p.toReal)
      (fun R => Filter.Eventually.of_forall (fun y => by
        apply ENNReal.rpow_le_rpow _ hp.le
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hdom R y)))
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt hg).ne
      (Filter.Eventually.of_forall (fun y => by
        have he := continuous_enorm.continuousAt.tendsto.comp (hpoint y)
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

theorem v12_testScale_le_one (R : ℕ) : v12_testScale R ≤ 1 := by
  unfold v12_testScale
  apply (div_le_one (by positivity)).2
  linarith [Nat.cast_nonneg (α := ℝ) R]

/-- Actual cutoff-derivative terms vanish in every finite nonzero Lp. -/
theorem v12_scaled_test_eLpNorm_tendsto
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (a : SchwartzMap V12Spatial ℝ) (k : SchwartzMap V12Spatial ℂ)
    (x : V12Spatial) (c : ℝ) (d : ℕ) (hd : 0 < d) :
    Tendsto (fun R => eLpNorm
      (fun y => (c * (v12_testScale R)^d) • v12_compactSpatialTest a k R x y)
      p volume) atTop (𝓝 0) := by
  let A : ℝ := SchwartzMap.seminorm ℝ 0 0 a
  have hA : 0 ≤ A := (norm_nonneg (a 0)).trans (SchwartzMap.norm_le_seminorm ℝ a 0)
  let H : V12Spatial → ℝ := fun y => (‖c‖ * A) • ‖k (x-y)‖
  have hk : MemLp (fun y => k (x-y)) p volume :=
    (k.memLp p volume).comp_measurePreserving (v12_subLeft_measurePreserving x)
  have hH : MemLp H p volume := hk.norm.const_smul (‖c‖ * A)
  apply v12_dominated_eLpNorm_tendsto_zero volume p hp0 hpt _ H hH
  · intro R
    have hc : Continuous (fun y =>
        (c * (v12_testScale R)^d) • v12_compactSpatialTest a k R x y) :=
      (v12_compactSpatialTest_smooth a (a.smooth (⊤ : ℕ∞)) k R x).continuous.const_smul _
    exact hc.aestronglyMeasurable
  · intro R y
    have hr : ‖(v12_testScale R)^d‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (v12_testScale_pos R).le d)]
      exact pow_le_one₀ (v12_testScale_pos R).le (v12_testScale_le_one R)
    have ha : ‖a (v12_testScale R • y)‖ ≤ A :=
      SchwartzMap.norm_le_seminorm ℝ a _
    have hsmall : ‖c * (v12_testScale R)^d‖ ≤ ‖c‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hr (norm_nonneg c)).trans_eq (mul_one _)
    calc
      _ = ‖c * (v12_testScale R)^d‖ * ‖a (v12_testScale R • y)‖ * ‖k (x-y)‖ := by
        simp only [v12_compactSpatialTest, v12_testCutoff, norm_smul, mul_assoc]
      _ ≤ (‖c‖ * A) * ‖k (x-y)‖ := by gcongr
      _ = ‖H y‖ := by
        simp [H, Real.norm_eq_abs, abs_of_nonneg hA, abs_of_nonneg (norm_nonneg c)]
  · intro y
    have hcoef : Tendsto (fun R => c * (v12_testScale R)^d) atTop (𝓝 0) := by
      simpa only [zero_pow (Nat.ne_of_gt hd), mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).mul
          (v12_testScale_tendsto.pow d)
    simpa only [zero_smul] using
      hcoef.smul (v12_compactSpatialTest_pointwise_tendsto a k x y)

/-- Addition of two genuinely vanishing Lp errors. -/
theorem v12_eLpNorm_add_tendsto_zero
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f g : ℕ → V12Spatial → ℂ)
    (hf : Tendsto (fun R => eLpNorm (f R) p volume) atTop (𝓝 0))
    (hg : Tendsto (fun R => eLpNorm (g R) p volume) atTop (𝓝 0)) :
    Tendsto (fun R => eLpNorm (f R + g R) p volume) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => bot_le) (fun R => eLpNorm_add_le (f := f R) (g := g R) hp)
  simpa only [zero_add] using hf.add hg

/-- The gradient error is computed from its actual Frechet derivative. -/
theorem v12_compactSpatialTest_fderiv_error_tendsto
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (χ : SchwartzMap V12Spatial ℝ) (hχ0 : χ 0 = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x m : V12Spatial) :
    Tendsto (fun R => eLpNorm
      (fun y => fderiv ℝ (v12_compactSpatialTest χ k R x) y m + (∂_{m} k) (x-y))
      p volume) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hp)
  have hsmall := v12_scaled_test_eLpNorm_tendsto p hp0 hpt (∂_{m} χ) k x 1 1 (by decide)
  have htail := v12_compactSpatialTest_error_tendsto p hp0 hpt χ χ.continuous hχ0 hχb
    (∂_{m} k) x
  have hneg : Tendsto (fun R => eLpNorm
      (fun y => -(v12_compactSpatialTest χ (∂_{m} k) R x y - (∂_{m} k) (x-y)))
      p volume) atTop (𝓝 0) := by
    simpa only [eLpNorm_neg] using htail
  have hsum := v12_eLpNorm_add_tendsto_zero p hp
    (fun R y => (1 * (v12_testScale R)^1) •
      v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x y)
    (fun R y => -(v12_compactSpatialTest χ (∂_{m} k) R x y - (∂_{m} k) (x-y)))
    hsmall hneg
  convert hsum using 1
  ext R
  congr 1
  funext y
  rw [v12_compactSpatialTest_fderiv_apply]
  simp only [pow_one, one_mul, Pi.add_apply]
  abel

/-- All three second-derivative cutoff contributions are retained. -/
theorem v12_compactSpatialTest_second_error_tendsto
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (χ : SchwartzMap V12Spatial ℝ) (hχ0 : χ 0 = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x m : V12Spatial) :
    Tendsto (fun R => eLpNorm
      (fun y => fderiv ℝ (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z m) y m -
        (∂_{m} (∂_{m} k)) (x-y)) p volume) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hp)
  have h₁ := v12_scaled_test_eLpNorm_tendsto p hp0 hpt (∂_{m} (∂_{m} χ)) k x 1 2 (by decide)
  have h₂ := v12_scaled_test_eLpNorm_tendsto p hp0 hpt (∂_{m} χ) (∂_{m} k) x (-2) 1 (by decide)
  have h₃ := v12_compactSpatialTest_error_tendsto p hp0 hpt χ χ.continuous hχ0 hχb
    (∂_{m} (∂_{m} k)) x
  have hsum := v12_eLpNorm_add_tendsto_zero p hp _ _
    (v12_eLpNorm_add_tendsto_zero p hp _ _ h₁ h₂) h₃
  convert hsum using 1
  ext R
  congr 1
  funext y
  rw [v12_compactSpatialTest_second_fderiv_apply]
  simp only [pow_one, one_mul, Pi.add_apply]
  module

#print axioms v12_dominated_eLpNorm_tendsto_zero
#print axioms v12_testScale_le_one
#print axioms v12_scaled_test_eLpNorm_tendsto
#print axioms v12_eLpNorm_add_tendsto_zero
#print axioms v12_compactSpatialTest_fderiv_error_tendsto
#print axioms v12_compactSpatialTest_second_error_tendsto

end SMScattering.W20Full
