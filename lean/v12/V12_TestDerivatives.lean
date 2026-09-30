import lean.v12.V12_TestCutoffApproximation

/-!
Actual first and second directional derivatives of the SAME compact test.
The identities differentiate chi(y/(R+1))*K(x-y), including the reflection
sign and both cutoff derivatives. Scale and reflection chain rules are
proved separately before the product rule. No derivative identity is an
input. Finite-Lp limits and the original PDE residual are separate steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory LineDeriv
open scoped Topology ENNReal ContDiff

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

/-- The exact scale derivative, obtained from HasFDerivAt composition. -/
theorem v12_schwartz_scale_fderiv_apply
    (χ : SchwartzMap V12Spatial ℝ) (r : ℝ) (y m : V12Spatial) :
    fderiv ℝ (fun z : V12Spatial => χ (r • z)) y m =
      r • fderiv ℝ (χ : V12Spatial → ℝ) (r • y) m := by
  have hscale := (hasFDerivAt_id (𝕜 := ℝ) y).const_smul r
  have h := (χ.hasFDerivAt (r • y)).comp y hscale
  have he := congrArg (fun T : V12Spatial →L[ℝ] ℝ => T m) h.fderiv
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using he

/-- The exact reflection derivative carries one minus sign. -/
theorem v12_schwartz_reflection_fderiv_apply
    (k : SchwartzMap V12Spatial ℂ) (x y m : V12Spatial) :
    fderiv ℝ (fun z : V12Spatial => k (x-z)) y m =
      -fderiv ℝ (k : V12Spatial → ℂ) (x-y) m := by
  have hreflect := (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x
  have h := (k.hasFDerivAt (x-y)).comp y hreflect
  have he := congrArg (fun T : V12Spatial →L[ℝ] ℂ => T m) h.fderiv
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using he

/-- Product rule applied only after the two chain rules are established. -/
theorem v12_compactSpatialTest_fderiv_apply
    (χ : SchwartzMap V12Spatial ℝ) (k : SchwartzMap V12Spatial ℂ)
    (R : ℕ) (x y m : V12Spatial) :
    fderiv ℝ (v12_compactSpatialTest χ k R x) y m =
      v12_testScale R •
        v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x y -
        v12_compactSpatialTest χ (∂_{m} k) R x y := by
  have hc : DifferentiableAt ℝ (fun z : V12Spatial => χ (v12_testScale R • z)) y := by
    fun_prop
  have hk : DifferentiableAt ℝ (fun z : V12Spatial => k (x-z)) y := by
    fun_prop
  rw [show v12_compactSpatialTest χ k R x =
      (fun z : V12Spatial => χ (v12_testScale R • z)) •
        (fun z : V12Spatial => k (x-z)) by funext z; rfl]
  rw [fderiv_smul hc hk]
  change χ (v12_testScale R • y) •
      fderiv ℝ (fun z : V12Spatial => k (x-z)) y m +
      fderiv ℝ (fun z : V12Spatial => χ (v12_testScale R • z)) y m • k (x-y) = _
  rw [v12_schwartz_scale_fderiv_apply, v12_schwartz_reflection_fderiv_apply]
  simp only [v12_compactSpatialTest, v12_testCutoff,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_neg, smul_smul, smul_eq_mul]
  ring

/-- The second derivative retains both cutoff terms and the cross term. -/
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
      fun z => v12_testScale R •
        v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x z -
        v12_compactSpatialTest χ (∂_{m} k) R x z := by
    funext z
    exact v12_compactSpatialTest_fderiv_apply χ k R x z m
  have h1 := (v12_compactSpatialTest_differentiable (∂_{m} χ) k R x).differentiableAt (x := y)
  have h2 := (v12_compactSpatialTest_differentiable χ (∂_{m} k) R x).differentiableAt (x := y)
  have hd := (h1.hasFDerivAt.const_smul (v12_testScale R)).sub h2.hasFDerivAt
  have he := congrArg (fun T : V12Spatial →L[ℝ] ℂ => T m) hd.fderiv
  have hcalc :
      fderiv ℝ (fun z => v12_testScale R •
        v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x z -
        v12_compactSpatialTest χ (∂_{m} k) R x z) y m =
      v12_testScale R •
        fderiv ℝ (v12_compactSpatialTest (∂_{m} χ : SchwartzMap V12Spatial ℝ) k R x) y m -
        fderiv ℝ (v12_compactSpatialTest χ (∂_{m} k) R x) y m := by
    simpa only [Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply] using he
  rw [hfun, hcalc, v12_compactSpatialTest_fderiv_apply, v12_compactSpatialTest_fderiv_apply]
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

theorem v12_compactSpatialTest_fderiv_pointwise_tendsto
    (χ : SchwartzMap V12Spatial ℝ) (hχ0 : χ 0 = 1)
    (k : SchwartzMap V12Spatial ℂ) (x y m : V12Spatial) :
    Tendsto (fun R => fderiv ℝ (v12_compactSpatialTest χ k R x) y m)
      atTop (𝓝 (-(∂_{m} k) (x-y))) := by
  have h := (v12_testScale_tendsto.smul
    (v12_compactSpatialTest_pointwise_tendsto (∂_{m} χ) k x y)).sub
      (v12_compactSpatialTest_pointwise_tendsto χ (∂_{m} k) x y)
  simpa only [v12_compactSpatialTest_fderiv_apply, hχ0, one_smul, zero_smul, zero_sub] using h

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
#print axioms v12_schwartz_scale_fderiv_apply
#print axioms v12_schwartz_reflection_fderiv_apply
#print axioms v12_compactSpatialTest_fderiv_apply
#print axioms v12_compactSpatialTest_second_fderiv_apply
#print axioms v12_compactSpatialTest_pointwise_tendsto
#print axioms v12_compactSpatialTest_fderiv_pointwise_tendsto
#print axioms v12_compactSpatialTest_second_pointwise_tendsto

end SMScattering.W20Full
