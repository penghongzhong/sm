import lean.v12.V12_YHodgeFarField
import lean.v12.V12_YHLSExternalStatement

/-! Concrete comparison of the paper's vector Hodge kernel with the scalar
fractional kernel. This is a paper-specific application step, not included
in the external HLS interface. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_rawHodgePotential (B : V12Spatial → ℝ) (x : V12Spatial) : V12Spatial :=
  ∫ y, B y • v12_hodgeKernel (x-y)

noncomputable def v12_positiveFractionalPotential (B : V12Spatial → ℝ) (x : V12Spatial) : ℝ :=
  ∫ y, ‖B y‖ / ‖x-y‖

theorem v12_hodge_integrand_norm (B : V12Spatial → ℝ) (x y : V12Spatial) :
    ‖B y • v12_hodgeKernel (x-y)‖ = (2 * Real.pi)⁻¹ * (‖B y‖ / ‖x-y‖) := by
  rw [norm_smul, v12_hodgeKernel_norm]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem v12_hodge_integrable_fractional_bound
    (B : V12Spatial → ℝ) (hB : AEStronglyMeasurable B (volume : Measure V12Spatial))
    (x : V12Spatial)
    (hi : Integrable (fun y => ‖B y‖ / ‖x-y‖) (volume : Measure V12Spatial)) :
    Integrable (fun y => B y • v12_hodgeKernel (x-y)) (volume : Measure V12Spatial) ∧
      ‖v12_rawHodgePotential B x‖ ≤ (2 * Real.pi)⁻¹ * v12_positiveFractionalPotential B x := by
  have hm := hB.smul
    (v12_hodgeKernel_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hdom := hi.const_mul (2 * Real.pi)⁻¹
  have hb : ∀ᵐ y ∂(volume : Measure V12Spatial),
      ‖B y • v12_hodgeKernel (x-y)‖ ≤ (2 * Real.pi)⁻¹ * (‖B y‖ / ‖x-y‖) :=
    Filter.Eventually.of_forall (fun y => (v12_hodge_integrand_norm B x y).le)
  refine ⟨hdom.mono' hm hb, ?_⟩
  exact (norm_integral_le_of_norm_le hdom hb).trans_eq (integral_const_mul _ _)

/-- The scalar comparison is exactly the positive input in registered HLS. -/
theorem v12_positiveFractionalPotential_eq_complex_norm
    (B : V12Spatial → ℝ) (x : V12Spatial)
    (hi : Integrable (fun y => ‖B y‖ / ‖x-y‖) (volume : Measure V12Spatial)) :
    v12_positiveFractionalPotential B x =
      ‖v12_fractionalPotential 1 (fun y => (‖B y‖ : ℂ)) x‖ := by
  have he : v12_fractionalPotential 1 (fun y => (‖B y‖ : ℂ)) x =
      ((v12_positiveFractionalPotential B x : ℝ) : ℂ) := by
    unfold v12_fractionalPotential v12_positiveFractionalPotential
    simp only [Real.rpow_one, ← Complex.ofReal_div]
    exact Complex.ofRealCLM.integral_comp_comm hi
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_of_nonneg (integral_nonneg (fun y => div_nonneg (norm_nonneg _) (norm_nonneg _)))).symm

#print axioms v12_hodge_integrand_norm
#print axioms v12_hodge_integrable_fractional_bound
#print axioms v12_positiveFractionalPotential_eq_complex_norm
end SMScattering.W20Full
