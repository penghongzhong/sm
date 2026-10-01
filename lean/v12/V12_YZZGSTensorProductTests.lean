import lean.v12.V12_YWUCanonicalSliceDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Concrete separated time/space tests for the original distributional PDE.
These are needed to identify the derivative of a compact spatial pairing
with its actual integrable source without smoothness of nonlocal coefficients.
No weak-time identity is postulated here. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open scoped Topology

def v12_tensorTest (η : ℝ → ℂ) (ψ : V12Spatial → ℂ) (z : V12Spacetime) : ℂ :=
  η z.1 * ψ z.2

theorem v12_tensorTest_support (η : ℝ → ℂ) (ψ : V12Spatial → ℂ) :
    tsupport (v12_tensorTest η ψ) ⊆ tsupport η ×ˢ tsupport ψ := by
  apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
  intro z hz
  have hn : η z.1 * ψ z.2 ≠ 0 := hz
  exact ⟨subset_closure (mul_ne_zero_iff.mp hn).1,
    subset_closure (mul_ne_zero_iff.mp hn).2⟩

theorem v12_tensorTest_compact (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hη : HasCompactSupport η) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (v12_tensorTest η ψ) :=
  (hη.prod hψ).of_isClosed_subset isClosed_closure (v12_tensorTest_support η ψ)

theorem v12_tensorTest_smooth (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v12_tensorTest η ψ) :=
  (hη.comp contDiff_fst).mul (hψ.comp contDiff_snd)

theorem v12_tensorTest_support_in_slab (a b : ℝ) (η : ℝ → ℂ)
    (ψ : V12Spatial → ℂ) (hη : tsupport η ⊆ Set.Ioo a b) :
    tsupport (v12_tensorTest η ψ) ⊆ Prod.fst ⁻¹' Set.Ioo a b := by
  intro z hz
  exact hη (v12_tensorTest_support η ψ hz).1

theorem v12_tensorTest_time_derivative (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (t : ℝ) (x : V12Spatial) :
    fderiv ℝ (v12_tensorTest η ψ) (t,x) v12_timeDirection = deriv η t * ψ x := by
  apply v12_joint_fderiv_time_slice
  · exact (v12_tensorTest_smooth η ψ hη hψ).differentiable (by simp) (t,x)
  · exact ((hη.differentiable (by simp) t).hasDerivAt).mul_const (ψ x)

theorem v12_tensorTest_spatial_derivative (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (t : ℝ) (x v : V12Spatial) :
    fderiv ℝ (v12_tensorTest η ψ) (t,x) (0,v) = η t * fderiv ℝ ψ x v := by
  rw [v12_joint_fderiv_spatial_slice _ t x v
    ((v12_tensorTest_smooth η ψ hη hψ).differentiable (by simp) (t,x))]
  change fderiv ℝ (fun y => η t * ψ y) x v = _
  rw [fderiv_const_mul (hψ.differentiable (by simp) x) (η t)]
  rfl

theorem v12_tensorTest_second_spatial_derivative (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (t : ℝ) (x v w : V12Spatial) :
    fderiv ℝ (fun z => fderiv ℝ (v12_tensorTest η ψ) z (0,v)) (t,x) (0,w) =
      η t * fderiv ℝ (fun y => fderiv ℝ ψ y v) x w := by
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun z => fderiv ℝ (v12_tensorTest η ψ) z (0,v)) =
      v12_tensorTest η (fun y => fderiv ℝ ψ y v) := by
    funext z
    exact v12_tensorTest_spatial_derivative η ψ hη hψ z.1 z.2 v
  rw [he]
  exact v12_tensorTest_spatial_derivative η _ hη hd t x w

#print axioms v12_tensorTest_second_spatial_derivative

#print axioms v12_tensorTest_compact
#print axioms v12_tensorTest_smooth
#print axioms v12_tensorTest_time_derivative
#print axioms v12_tensorTest_spatial_derivative
end SMScattering.W20Full
