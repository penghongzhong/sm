import lean.v12.V12_YRActualCurvatureBounds
import lean.v12.V12_YHodgeFarField

/-! The far-field Hodge bound for the actual curvature of the raw field.
No density budget is supplied independently of the field energy. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_actual_curvature_integral_bound
    (q : V12Spatial → V12Field) (hq : MemLp q 2 (volume : Measure V12Spatial))
    (M : ℝ) (hM : 0 ≤ M)
    (hE : eLpNorm q 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M) :
    Integrable (fun y => v12_curvatureDensity (q y)) (volume : Measure V12Spatial) ∧
      (∫ y, ‖v12_curvatureDensity (q y)‖) ≤ 2 * M ^ 2 := by
  have hq' : MemLp q (1 * 2) (volume : Measure V12Spatial) := by simpa using hq
  have hB := (memLp_one_iff_integrable).mp
    (v12_curvatureDensity_memLp (volume : Measure V12Spatial) q 1 hq')
  refine ⟨hB, ?_⟩
  have he := v12_curvatureDensity_energy_bound q hq (ENNReal.ofReal M) hE
  have hf : 2 * (ENNReal.ofReal M) ^ 2 ≠ ∞ := by finiteness
  have ht := ENNReal.toReal_mono hf he
  rw [eLpNorm_one_eq_lintegral_enorm hB.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hB.aestronglyMeasurable] at ht
  simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hM] using ht

theorem v12_actual_hodge_far_bound
    (q : V12Spatial → V12Field) (hq : MemLp q 2 (volume : Measure V12Spatial))
    (M : ℝ) (hM : 0 ≤ M)
    (hE : eLpNorm q 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M)
    (R L : ℝ) (hL : 0 < L) (hRL : 2 * R ≤ L)
    (x : V12Spatial) (hx : ‖x‖ ≤ R) :
    let ν := (volume : Measure V12Spatial).restrict {y | L ≤ ‖y‖}
    Integrable (fun y => v12_curvatureDensity (q y) • v12_hodgeKernel (x-y)) ν ∧
      ‖∫ y, v12_curvatureDensity (q y) • v12_hodgeKernel (x-y) ∂ν‖ ≤
        (Real.pi * L)⁻¹ * (2 * M ^ 2) := by
  obtain ⟨hB, hBE⟩ := v12_actual_curvature_integral_bound q hq M hM hE
  obtain ⟨hi, hb⟩ := v12_hodge_far_integrable_and_bound R L hL hRL x hx
    (fun y => v12_curvatureDensity (q y)) hB
  refine ⟨hi, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun y => norm_nonneg (v12_curvatureDensity (q y)))) hB.norm).trans hBE

#print axioms v12_actual_curvature_integral_bound
#print axioms v12_actual_hodge_far_bound
end SMScattering.W20Full
