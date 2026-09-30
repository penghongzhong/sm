import lean.v12.V12_YHodgeFarField
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
The actual truncated two-dimensional Hodge kernel belongs to L^(4/3).
The singularity is checked against dimension2 with Mathlib's proved radial
integrability theorem; no local-kernel Lp assumption is introduced.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_hodgeKernel_ball_power_integrable (R p : ℝ) (hp : p < 2) :
    IntegrableOn (fun z : V12Spatial => ‖v12_hodgeKernel z‖ ^ p)
      (Metric.ball 0 R) (volume : Measure V12Spatial) := by
  refine integrableOn_ball_of_norm_le_rpow
    (C := (2 * Real.pi) ^ (-p)) (α := p) (by simp [V12Spatial]) ?_ ?_ ?_
  · simpa [V12Spatial] using hp
  · apply Filter.Eventually.of_forall
    intro z
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [v12_hodgeKernel_norm, ← Real.rpow_neg_eq_inv_rpow,
      Real.mul_rpow (by positivity) (norm_nonneg _)]
  · have hm : Measurable (fun z : V12Spatial => ‖v12_hodgeKernel z‖ ^ p) :=
      v12_hodgeKernel_measurable.norm.pow_const p
    exact hm.aestronglyMeasurable

theorem v12_hodgeKernel_truncated_memLp (R : ℝ) :
    MemLp ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel)
      ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) := by
  rw [memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet]
  have hp0 : (4 : ℝ≥0∞) / 3 ≠ 0 := by norm_num
  have hptop : (4 : ℝ≥0∞) / 3 ≠ ∞ := by finiteness
  apply (integrable_norm_rpow_iff
    v12_hodgeKernel_measurable.aestronglyMeasurable.restrict hp0 hptop).mp
  have hp : ((4 : ℝ≥0∞) / 3).toReal = (4 : ℝ) / 3 := by
    norm_num [ENNReal.toReal_div]
  rw [hp]
  exact v12_hodgeKernel_ball_power_integrable R ((4 : ℝ) / 3) (by norm_num)

#print axioms v12_hodgeKernel_ball_power_integrable
#print axioms v12_hodgeKernel_truncated_memLp
end SMScattering.W20Full
