import lean.v12.V12_SourceProducts
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
The actual derivative of F_j = A_j Q and its Coulomb cancellation.
The divergence identity is proved by the product rule at the same point;
no source identity is accepted as an external interface.
-/

set_option autoImplicit false

namespace SMScattering.W20Full

/-- Product rule for the concrete drift product used by the Lp source. -/
theorem v12_driftProduct_fderiv_apply
    (A : Fin 2 → V12Spatial → ℂ) (Q : V12Spatial → V12Field)
    (j : Fin 2) (x v : V12Spatial)
    (hA : DifferentiableAt ℝ (A j) x) (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (v12_driftProduct A Q j) x v =
      A j x • fderiv ℝ Q x v + fderiv ℝ (A j) x v • Q x := by
  change fderiv ℝ (fun y => A j y • Q y) x v = _
  rw [fderiv_fun_smul hA hQ]
  rfl

/-- The two derivatives of the actual products have no div(A) remainder. -/
theorem v12_coulomb_drift_divergence
    (A : Fin 2 → V12Spatial → ℂ) (Q : V12Spatial → V12Field)
    (x v₀ v₁ : V12Spatial)
    (hA : ∀ j, DifferentiableAt ℝ (A j) x)
    (hQ : DifferentiableAt ℝ Q x)
    (hdiv : fderiv ℝ (A 0) x v₀ + fderiv ℝ (A 1) x v₁ = 0) :
    fderiv ℝ (v12_driftProduct A Q 0) x v₀ +
      fderiv ℝ (v12_driftProduct A Q 1) x v₁ =
      A 0 x • fderiv ℝ Q x v₀ + A 1 x • fderiv ℝ Q x v₁ := by
  rw [v12_driftProduct_fderiv_apply A Q 0 x v₀ (hA 0) hQ,
    v12_driftProduct_fderiv_apply A Q 1 x v₁ (hA 1) hQ]
  calc
    _ = (A 0 x • fderiv ℝ Q x v₀ + A 1 x • fderiv ℝ Q x v₁) +
        (fderiv ℝ (A 0) x v₀ + fderiv ℝ (A 1) x v₁) • Q x := by
      rw [add_smul]
      abel
    _ = _ := by rw [hdiv, zero_smul, add_zero]

#print axioms v12_driftProduct_fderiv_apply
#print axioms v12_coulomb_drift_divergence

end SMScattering.W20Full
