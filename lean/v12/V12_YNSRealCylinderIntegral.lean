import lean.v12.V12_YNRealCylinderRestriction

/-! Transfer of actual L1 norm integrals to all real spatial radii. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_local_integral_norm_limit_all_real_radii
    {E : Type} [NormedAddCommGroup E]
    (a b : ℝ) (f : ℕ → V12Spacetime → E)
    (hf : ∀ R n, Integrable (f n) ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => ∫ z, ‖f n z‖
      ∂((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) atTop (𝓝 0))
    (r : ℝ) :
    (∀ n, Integrable (f n) ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))) ∧
    Tendsto (fun n => ∫ z, ‖f n z‖
      ∂((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := v12_real_cylinder_subset r
  have hμ := Measure.restrict_mono (μ := v12_slab_measure a b) hR le_rfl
  refine ⟨fun n => (hf R n).mono_measure hμ, ?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun z => norm_nonneg _)) _ (hlim R)
  intro n
  exact integral_mono_measure hμ (Filter.Eventually.of_forall (fun z => norm_nonneg _)) (hf R n).norm

#print axioms v12_local_integral_norm_limit_all_real_radii
end SMScattering.W20Full
