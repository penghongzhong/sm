import lean.v12.V12_KernelConvolutionIdentity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact angular-frequency inverse-integral formula for the existing cutoff.
The cyclic scale already contains 2π. This lemma supplies the change of
variables, including its two-dimensional Jacobian, rather than identifying
Fourier conventions by a comment. Candidate until actual Lean compilation. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped FourierTransform

theorem v12_cyclicScale_angular_argument (N : ℕ) (η : V12Spatial) :
    v12_cyclicScale N • η = ((2 : ℝ) ^ N)⁻¹ • ((2 * Real.pi) • η) := by
  rw [smul_smul]
  congr 1
  simp only [v12_cyclicScale, div_eq_mul_inv]
  ring

theorem v12_cutoffKernel_angular_integral
    (p : V12Spatial → ℝ) (hc : HasCompactSupport p)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (N : ℕ) (x : V12Spatial) :
    v12_cutoffKernelSchwartz p hc hs N x =
      ((2 * Real.pi) ^ 2)⁻¹ •
        (∫ ξ : V12Spatial, Complex.exp ((inner ℝ ξ x : ℂ) * Complex.I) *
          (p (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ)) := by
  let F : V12Spatial → ℂ := fun ξ =>
    Complex.exp ((inner ℝ ξ x : ℂ) * Complex.I) *
      (p (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ)
  have he : v12_cutoffKernelSchwartz p hc hs N x =
      ∫ η : V12Spatial, F ((2 * Real.pi) • η) := by
    change (𝓕⁻ (v12_scaledCutoffSchwartz p hc hs N)) x = _
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun η => by
      simp only [F, v12_scaledCutoffSchwartz_apply, smul_eq_mul,
        real_inner_smul_left, v12_cyclicScale_angular_argument])
  rw [he, Measure.integral_comp_smul_of_nonneg volume F (2 * Real.pi)
    (hR := by positivity)]
  simpa only [V12Spatial, finrank_euclideanSpace_fin] using (rfl :
    ((2 * Real.pi) ^ 2)⁻¹ • (∫ ξ : V12Spatial, F ξ) =
      ((2 * Real.pi) ^ 2)⁻¹ • (∫ ξ : V12Spatial, F ξ))

#print axioms v12_cyclicScale_angular_argument
#print axioms v12_cutoffKernel_angular_integral
end SMScattering.W20Full
