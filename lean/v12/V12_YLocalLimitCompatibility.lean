import lean.v12.V12_FrequencyTightnessLimit

/-!
Nested-cylinder compatibility of limits from the SAME global sequence.
The restriction map is built directly from the measure inequality, avoiding
transports between iterated restricted measures. Compatibility is a conclusion,
not an input. Measurable gluing remains a separate construction.
-/

set_option autoImplicit false

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_cylinder_measure_mono (a b : ℝ) {R S : ℕ} (hRS : R ≤ S) :
    (v12_slab_measure a b).restrict (v12_spatial_cylinder R) ≤
      (v12_slab_measure a b).restrict (v12_spatial_cylinder S) := by
  apply Measure.restrict_mono _ le_rfl
  intro z hz
  exact lt_of_lt_of_le hz (add_le_add_right (by exact_mod_cast hRS) 1)

noncomputable def v12_nested_localize (a b : ℝ) {R S : ℕ} (hRS : R ≤ S) :
    V12CylinderL2 a b S →L[ℝ] V12CylinderL2 a b R :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using v12_cylinder_measure_mono a b hRS)

theorem v12_nested_localize_coeFn (a b : ℝ) {R S : ℕ} (hRS : R ≤ S)
    (q : V12CylinderL2 a b S) :
    (v12_nested_localize a b hRS q : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] q :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ q

theorem v12_nested_localize_global (a b : ℝ) {R S : ℕ} (hRS : R ≤ S)
    (q : V12SlabL2 a b) :
    v12_nested_localize a b hRS (v12_localize a b S q) = v12_localize a b R q := by
  apply Lp.ext_iff.mpr
  have hS := (v12_localize_coeFn a b S q).filter_mono
    (ae_mono (v12_cylinder_measure_mono a b hRS))
  exact (v12_nested_localize_coeFn a b hRS _).trans
    (hS.trans (v12_localize_coeFn a b R q).symm)

/-- Limits of one global sequence agree under actual nested restriction. -/
theorem v12_local_limits_compatible (a b : ℝ) {R S : ℕ} (hRS : R ≤ S)
    (u : ℕ → V12SlabL2 a b)
    (qR : V12CylinderL2 a b R) (qS : V12CylinderL2 a b S)
    (hR : Tendsto (fun n => v12_localize a b R (u n)) atTop (𝓝 qR))
    (hS : Tendsto (fun n => v12_localize a b S (u n)) atTop (𝓝 qS)) :
    v12_nested_localize a b hRS qS = qR := by
  have h := ((v12_nested_localize a b hRS).continuous.tendsto qS).comp hS
  have h' : Tendsto (fun n => v12_localize a b R (u n)) atTop
      (𝓝 (v12_nested_localize a b hRS qS)) := by
    simpa only [Function.comp_def, v12_nested_localize_global] using h
  exact tendsto_nhds_unique h' hR

/-- Equality of the representatives on the smaller cylinder is derived. -/
theorem v12_local_limits_ae_compatible (a b : ℝ) {R S : ℕ} (hRS : R ≤ S)
    (u : ℕ → V12SlabL2 a b)
    (qR : V12CylinderL2 a b R) (qS : V12CylinderL2 a b S)
    (hR : Tendsto (fun n => v12_localize a b R (u n)) atTop (𝓝 qR))
    (hS : Tendsto (fun n => v12_localize a b S (u n)) atTop (𝓝 qS)) :
    (qR : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] qS := by
  rw [← v12_local_limits_compatible a b hRS u qR qS hR hS]
  exact v12_nested_localize_coeFn a b hRS qS

#print axioms v12_cylinder_measure_mono
#print axioms v12_nested_localize_coeFn
#print axioms v12_nested_localize_global
#print axioms v12_local_limits_compatible
#print axioms v12_local_limits_ae_compatible

end SMScattering.W20Full
