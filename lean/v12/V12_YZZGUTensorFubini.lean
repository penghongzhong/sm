import lean.v12.V12_YZZGSTensorProductTests
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual Fubini identity for separated tests, including integrability of
the resulting time integrand. The equalities concern the original functions,
not arbitrary representatives with matching norms. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory

 theorem v12_tensor_integral_fubini
    (a b : ℝ) (r : V12Spacetime → ℂ) (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hi : Integrable (fun z => r z * (η z.1 * ψ z.2)) (v12_slab_measure a b)) :
    Integrable (fun t => η t * (∫ x : V12Spatial, r (t,x) * ψ x))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
    (∫ z, r z * (η z.1 * ψ z.2) ∂v12_slab_measure a b) =
      ∫ t, η t * (∫ x : V12Spatial, r (t,x) * ψ x)
        ∂(volume : Measure ℝ).restrict (Set.Icc a b) := by
  have he (t : ℝ) : (∫ x : V12Spatial, r (t,x) * (η t * ψ x)) =
      η t * (∫ x : V12Spatial, r (t,x) * ψ x) := by
    calc
      _ = ∫ x : V12Spatial, η t * (r (t,x) * ψ x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := integral_const_mul _ _
  have htime := hi.integral_prod_left
  refine ⟨?_, ?_⟩
  · simpa only [he] using htime
  · change (∫ z, r z * (η z.1 * ψ z.2)
      ∂((volume : Measure ℝ).restrict (Set.Icc a b)).prod (volume : Measure V12Spatial)) = _
    rw [integral_prod _ hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall he

theorem v12_locally_integrable_tensor_fubini
    (a b : ℝ) (r : V12Spacetime → ℂ) (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hr : LocallyIntegrable r (v12_slab_measure a b))
    (hη : Continuous η) (hcη : HasCompactSupport η)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun t => η t * (∫ x : V12Spatial, r (t,x) * ψ x))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
    (∫ z, r z * (η z.1 * ψ z.2) ∂v12_slab_measure a b) =
      ∫ t, η t * (∫ x : V12Spatial, r (t,x) * ψ x)
        ∂(volume : Measure ℝ).restrict (Set.Icc a b) := by
  have hc := v12_tensorTest_compact η ψ hcη hcψ
  have hcont : Continuous (v12_tensorTest η ψ) :=
    (hη.comp continuous_fst).mul (hψ.comp continuous_snd)
  have hi := hr.integrable_smul_right_of_hasCompactSupport hcont hc
  apply v12_tensor_integral_fubini a b r η ψ
  simpa only [smul_eq_mul, v12_tensorTest] using hi

#print axioms v12_tensor_integral_fubini
#print axioms v12_locally_integrable_tensor_fubini
end SMScattering.W20Full
