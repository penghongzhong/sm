import lean.v12.V12_YZZGLocalSmoothIntegration

/-! A locally smooth field times a compact test is a genuine global smooth
compact test. This permits using distributional div A = 0 without assuming
joint smoothness of the nonlocal connection. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory Filter
open scoped Topology ENNReal

theorem v12_local_smooth_mul_compact_test
    (U : Set V12Spacetime) (hU : IsOpen U) (f ψ : V12Spacetime → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f z*ψ z) ∧
      HasCompactSupport (fun z => f z*ψ z) ∧
      tsupport (fun z => f z*ψ z) ⊆ U := by
  refine ⟨contDiff_iff_contDiffAt.mpr ?_, hc.mul_left, tsupport_mul_subset_right.trans hs⟩
  intro z
  by_cases hz : z ∈ U
  · exact (hf.contDiffAt (hU.mem_nhds hz)).mul hψ.contDiffAt
  · have hn : z ∉ tsupport ψ := fun h => hz (hs h)
    have hne : ∀ᶠ y in 𝓝 z, y ∉ tsupport ψ :=
      isClosed_closure.isOpen_compl.mem_nhds hn
    apply contDiffAt_const.congr_of_eventuallyEq
    exact Filter.Eventually.mono hne (fun y hy => by
      change f y * ψ y = (0 : ℂ)
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero])

theorem v12_local_smooth_compact_product_derivative
    (U : Set V12Spacetime) (hU : IsOpen U) (f ψ : V12Spacetime → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hs : tsupport ψ ⊆ U) (z v : V12Spacetime) :
    fderiv ℝ (fun y => f y*ψ y) z v =
      fderiv ℝ f z v * ψ z + f z * fderiv ℝ ψ z v := by
  by_cases hz : z ∈ U
  · rw [fderiv_fun_mul
      ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz))
      (hψ.differentiable (by simp)).differentiableAt]
    change f z * fderiv ℝ ψ z v + ψ z * fderiv ℝ f z v = _
    ring
  · have hn : z ∉ tsupport ψ := fun h => hz (hs h)
    have hprod : z ∉ tsupport (fun y => f y*ψ y) :=
      fun h => hn (tsupport_mul_subset_right h)
    rw [fderiv_of_notMem_tsupport ℝ hprod,
      fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn]
    simp

#print axioms v12_local_smooth_mul_compact_test
#print axioms v12_local_smooth_compact_product_derivative
end SMScattering.W20Full
