import lean.v12.V12_YCoulombDivergenceSource
import lean.v12.V12_ZFActualTestPDETimeIdentity

/-!
Concrete Coulomb drift products in the raw PDE. This proves the conversion
needed by the compact-test/cutoff time-identity chain. The original smooth
Coulomb equation and Hodge reconstruction are upstream obligations.
-/

set_option autoImplicit false

namespace SMScattering.W20Full

/-- The divergence RHS agrees with the original first-order drift RHS. -/
theorem v12_rawDivergenceRHS_coulomb
    (A : Fin 2 → V12Spatial → ℂ) (q g : V12Spatial → V12Field)
    (x : V12Spatial)
    (hA : ∀ j, DifferentiableAt ℝ (A j) x)
    (hq : DifferentiableAt ℝ q x)
    (hdiv : fderiv ℝ (A 0) x (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (A 1) x (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    v12_rawDivergenceRHS q (v12_driftProduct A q) g x =
      Complex.I • (fderiv ℝ (fun z => fderiv ℝ q z (e 0)) x (e 0) +
        fderiv ℝ (fun z => fderiv ℝ q z (e 1)) x (e 1)) +
      (2 : ℂ) • (A 0 x • fderiv ℝ q x (e 0) +
        A 1 x • fderiv ℝ q x (e 1)) + (-Complex.I) • g x := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hd := v12_coulomb_drift_divergence A q x (e 0) (e 1) hA hq hdiv
  unfold v12_rawDivergenceRHS
  dsimp only
  rw [add_assoc (Complex.I • _) ((2 : ℂ) • _) ((2 : ℂ) • _), ← smul_add, hd]

#print axioms v12_rawDivergenceRHS_coulomb

end SMScattering.W20Full
