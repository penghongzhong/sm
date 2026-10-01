import lean.v12.V12_YZZGROriginalDistributionTests
import lean.v12.V12_YZZGSTensorProductTests

/-! The original advective distributional PDE and weak Coulomb constraint
are tested with the concrete time-space product. This derives the localized
actual time-source identity without differentiating A or assuming that
identity as an interface. Fubini/source-class application remains downstream. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_PDE_tensor_time_source
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g : V12Spacetime → ℂ) (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hA : ∀ j, LocallyIntegrable (A j) (v12_slab_measure a b))
    (hg : MemLp g ((4 : ℝ≥0∞)/3) (v12_slab_measure a b))
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Set.Ioo a b)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hdiv : ∀ φ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, A 0 z * fderiv ℝ φ z (v12_spatialDirection 0) ∂v12_slab_measure a b) +
      (∫ z, A 1 z * fderiv ℝ φ z (v12_spatialDirection 1) ∂v12_slab_measure a b) = 0)
    (hPDE : V12OriginalScalarDistributionalPDE a b f A g
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1)) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    (∫ z, fderiv ℝ f z v12_timeDirection * (η z.1 * ψ z.2) ∂v12_slab_measure a b) =
      Complex.I *
        ((∫ z, f z * (η z.1 * fderiv ℝ (fun y => fderiv ℝ ψ y (e 0)) z.2 (e 0))
          ∂v12_slab_measure a b) +
         (∫ z, f z * (η z.1 * fderiv ℝ (fun y => fderiv ℝ ψ y (e 1)) z.2 (e 1))
          ∂v12_slab_measure a b)) -
      2 * ((∫ z, (A 0 z * f z) * (η z.1 * fderiv ℝ ψ z.2 (e 0)) ∂v12_slab_measure a b) +
           (∫ z, (A 1 z * f z) * (η z.1 * fderiv ℝ ψ z.2 (e 1)) ∂v12_slab_measure a b)) -
      Complex.I * (∫ z, g z * (η z.1 * ψ z.2) ∂v12_slab_measure a b) := by
  dsimp only
  let Φ := v12_tensorTest η ψ
  have hΦ := v12_tensorTest_smooth η ψ hη hψ
  have hcΦ := v12_tensorTest_compact η ψ hcη hcψ
  have hsΦ := v12_tensorTest_support_in_slab a b η ψ hsη
  have he := v12_compact_PDE_from_original_distribution a b f A g Φ
    v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1)
    hf hA hg hΦ hcΦ hsΦ hdiv hPDE
  have ht := v12_original_slab_compact_IBP a b f Φ hf hΦ hcΦ hsΦ v12_timeDirection
  rw [ht] at he
  have hfirst (j : Fin 2) (z : V12Spacetime) :
      fderiv ℝ Φ z (v12_spatialDirection j) =
      η z.1 * fderiv ℝ ψ z.2 (EuclideanSpace.basisFun (Fin 2) ℝ j) :=
    v12_tensorTest_spatial_derivative η ψ hη hψ z.1 z.2 _
  have hsecond (j : Fin 2) (z : V12Spacetime) :
      fderiv ℝ (fun y => fderiv ℝ Φ y (v12_spatialDirection j)) z
        (v12_spatialDirection j) =
      η z.1 * fderiv ℝ
        (fun y => fderiv ℝ ψ y (EuclideanSpace.basisFun (Fin 2) ℝ j)) z.2
        (EuclideanSpace.basisFun (Fin 2) ℝ j) :=
    v12_tensorTest_second_spatial_derivative η ψ hη hψ z.1 z.2 _ _
  simp only [hsecond] at he
  simp only [hfirst, Φ, v12_tensorTest] at he
  linear_combination (norm := ring_nf) -Complex.I * he
  simp only [Complex.I_sq] <;> ring

#print axioms v12_original_PDE_tensor_time_source
end SMScattering.W20Full
