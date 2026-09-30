import lean.v12.V12_TestCutoffApproximation

/-!
Actual first and second directional derivatives of the SAME compact test.
The identities differentiate chi(y/(R+1))*K(x-y), including the reflection
sign and both cutoff derivatives. No derivative identity is an assumption.
Finite-Lp convergence and the original PDE residual are separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory LineDeriv
open scoped Topology ENNReal ContDiff

/-- Exact real Schwartz realization of the original smooth compact cutoff. -/
noncomputable def v12_realCutoffSchwartz (χ : V12Spatial → ℝ)
    (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    SchwartzMap V12Spatial ℝ := hc.toSchwartzMap hs

@[simp] theorem v12_realCutoffSchwartz_apply (χ : V12Spatial → ℝ)
    (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (y : V12Spatial) :
    v12_realCutoffSchwartz χ hc hs y = χ y := rfl

theorem v12_compactSpatialTest_differentiable
    (χ : SchwartzMap V12Spatial ℝ) (k : SchwartzMap V12Spatial ℂ)
    (R : ℕ) (x : V12Spatial) :
    Differentiable ℝ (v12_compactSpatialTest χ k R x) := by
  exact (v12_compactSpatialTest_smooth χ (χ.smooth (⊤ : ℕ∞)) k R x).differentiable
    (by norm_num)

/-- Exact first derivative, with the negative reflection sign. -/
theorem v12_compactSpatialTest_fderiv_apply
    (χ : SchwartzMap V12Spatial ℝ) (k : SchwartzMap V12Spatial ℂ)
    (R : ℕ) (x y m : V12Spatial) :
    fderiv ℝ (v12_compactSpatialTest χ k R x) y m =
      v12_testScale R •
        v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x y -
        v12_compactSpatialTest χ (∂_{m} k) R x y := by
  have hscale := (hasFDerivAt_id (𝕜 := ℝ) y).const_smul (v12_testScale R)
  have hreflect := (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x
  have hc := (χ.hasFDerivAt (v12_testScale R • y)).comp y hscale
  have hk := (k.hasFDerivAt (x - y)).comp y hreflect
  have hp := hc.smul hk
  have hder := hp.fderiv
  dsimp only [Function.comp_def, Pi.smul_apply] at hder
  change fderiv ℝ (fun z : V12Spatial => χ (v12_testScale R • z) • k (x-z)) y m = _
  rw [hder]
  simp [ContinuousLinearMap.comp_apply, v12_compactSpatialTest, v12_testCutoff,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_smul, smul_eq_mul, sub_eq_add_neg, add_comm]

/-- Exact second derivative retaining both cutoff and cross terms. -/
theorem v12_compactSpatialTest_second_fderiv_apply
    (χ : SchwartzMap V12Spatial ℝ) (k : SchwartzMap V12Spatial ℂ)
    (R : ℕ) (x y m : V12Spatial) :
    fderiv ℝ (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z m) y m =
      (v12_testScale R)^2 •
        v12_compactSpatialTest (∂_{m} (∂_{m} χ) : SchwartzMap V12Spatial ℝ) k R x y -
        (2 * v12_testScale R) •
        v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) (∂_{m} k) R x y +
        v12_compactSpatialTest χ (∂_{m} (∂_{m} k)) R x y := by
  have hfun : (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z m) =
      v12_testScale R •
        v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x -
        v12_compactSpatialTest χ (∂_{m} k) R x := by
    funext z
    exact v12_compactSpatialTest_fderiv_apply χ k R x z m
  have h₁ := (v12_compactSpatialTest_differentiable (∂_{m} χ) k R x).differentiableAt (x := y)
  have h₂ := (v12_compactSpatialTest_differentiable χ (∂_{m} k) R x).differentiableAt (x := y)
  rw [hfun, fderiv_sub (h₁.const_smul (v12_testScale R)) h₂,
    fderiv_const_smul h₁]
  change v12_testScale R •
      fderiv ℝ (v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x) y m -
      fderiv ℝ (v12_compactSpatialTest χ (∂_{m} k) R x) y m = _
  rw [v12_compactSpatialTest_fderiv_apply, v12_compactSpatialTest_fderiv_apply]
  module

/-- Fixed-x pointwise limit for arbitrary real Schwartz multipliers. -/
theorem v12_compactSpatialTest_pointwise_tendsto
    (χ : SchwartzMap V12Spatial ℝ) (k : SchwartzMap V12Spatial ℂ)
    (x y : V12Spatial) :
    Tendsto (fun R => v12_compactSpatialTest χ k R x y) atTop
      (𝓝 (χ 0 • k (x-y))) := by
  have hy : Tendsto (fun R => v12_testScale R • y) atTop (𝓝 (0 : V12Spatial)) := by
    simpa only [zero_smul] using v12_testScale_tendsto.smul_const y
  exact ((χ.continuous.tendsto 0).comp hy).smul_const (k (x-y))

/-- The first-derivative limit is minus the reflected kernel derivative. -/
theorem v12_compactSpatialTest_fderiv_pointwise_tendsto
    (χ : SchwartzMap V12Spatial ℝ) (hχ0 : χ 0 = 1)
    (k : SchwartzMap V12Spatial ℂ) (x y m : V12Spatial) :
    Tendsto (fun R => fderiv ℝ (v12_compactSpatialTest χ k R x) y m)
      atTop (𝓝 (-(∂_{m} k) (x-y))) := by
  have h := (v12_testScale_tendsto.smul
    (v12_compactSpatialTest_pointwise_tendsto (∂_{m} χ) k x y)).sub
      (v12_compactSpatialTest_pointwise_tendsto χ (∂_{m} k) x y)
  simpa only [v12_compactSpatialTest_fderiv_apply, hχ0, one_smul, zero_smul, zero_sub] using h

/-- Reflection twice gives a positive second derivative. -/
theorem v12_compactSpatialTest_second_pointwise_tendsto
    (χ : SchwartzMap V12Spatial ℝ) (hχ0 : χ 0 = 1)
    (k : SchwartzMap V12Spatial ℂ) (x y m : V12Spatial) :
    Tendsto (fun R =>
      fderiv ℝ (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z m) y m)
      atTop (𝓝 ((∂_{m} (∂_{m} k)) (x-y))) := by
  have h₁ := (v12_testScale_tendsto.pow 2).smul
    (v12_compactSpatialTest_pointwise_tendsto (∂_{m} (∂_{m} χ)) k x y)
  have h₂ := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
    v12_testScale_tendsto).smul
    (v12_compactSpatialTest_pointwise_tendsto (∂_{m} χ) (∂_{m} k) x y)
  have h₃ := v12_compactSpatialTest_pointwise_tendsto χ (∂_{m} (∂_{m} k)) x y
  have h := (h₁.sub (show Tendsto
      (fun R => (2 * v12_testScale R) •
        v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) (∂_{m} k) R x y)
      atTop (𝓝 ((2 * (0 : ℝ)) • ((∂_{m} χ) 0 • (∂_{m} k) (x-y)))) from h₂)).add h₃
  simpa only [v12_compactSpatialTest_second_fderiv_apply, hχ0, one_smul,
    zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_smul, sub_zero, zero_add] using h

#print axioms v12_realCutoffSchwartz_apply
#print axioms v12_compactSpatialTest_differentiable
#print axioms v12_compactSpatialTest_fderiv_apply
#print axioms v12_compactSpatialTest_second_fderiv_apply
#print axioms v12_compactSpatialTest_pointwise_tendsto
#print axioms v12_compactSpatialTest_fderiv_pointwise_tendsto
#print axioms v12_compactSpatialTest_second_pointwise_tendsto

end SMScattering.W20Full
