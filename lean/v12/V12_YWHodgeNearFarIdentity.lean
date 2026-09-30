import lean.v12.V12_YJYoungRawRepresentative
import lean.v12.V12_YSHodgeFractionalDomination

/-! The near/far decomposition is proved for the original Hodge integral,
including the exact density and kernel cutoffs used in Young's inequality. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_rawNearHodge_eq_density_cutoff
    (R L : ℝ) (x : V12Spatial) (hx : ‖x‖ ≤ R) (B : V12Spatial → ℝ) :
    v12_rawNearHodge (R+L) ((Metric.ball (0 : V12Spatial) L).indicator B) x =
      ∫ y in Metric.ball (0 : V12Spatial) L, B y • v12_hodgeKernel (x-y) := by
  unfold v12_rawNearHodge
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : y ∈ Metric.ball (0 : V12Spatial) L
  · have hnorm : ‖y‖ < L := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    have hxy : x-y ∈ Metric.ball (0 : V12Spatial) (R+L) := by
      simp only [Metric.mem_ball, dist_zero_right]
      exact (norm_sub_le x y).trans_lt (add_lt_add_of_le_of_lt hx hnorm)
    simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hxy]
  · simp only [Set.indicator_of_notMem hy, zero_smul]

theorem v12_actualHodge_near_far
    (R L : ℝ) (x : V12Spatial) (hx : ‖x‖ ≤ R) (B : V12Spatial → ℝ)
    (hi : Integrable (fun y => B y • v12_hodgeKernel (x-y)) (volume : Measure V12Spatial)) :
    v12_rawHodgePotential B x =
      v12_rawNearHodge (R+L) ((Metric.ball (0 : V12Spatial) L).indicator B) x +
        ∫ y in {y : V12Spatial | L ≤ ‖y‖}, B y • v12_hodgeKernel (x-y) := by
  rw [v12_rawNearHodge_eq_density_cutoff R L x hx B]
  have hset : {y : V12Spatial | L ≤ ‖y‖} = (Metric.ball (0 : V12Spatial) L)ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
  rw [hset]
  exact (integral_add_compl measurableSet_ball hi).symm

theorem v12_actualHodge_near_error_bound
    (R L : ℝ) (hL : 0 < L) (hRL : 2*R ≤ L)
    (x : V12Spatial) (hx : ‖x‖ ≤ R) (B : V12Spatial → ℝ)
    (hB : Integrable B (volume : Measure V12Spatial))
    (hi : Integrable (fun y => B y • v12_hodgeKernel (x-y)) (volume : Measure V12Spatial)) :
    ‖v12_rawHodgePotential B x -
      v12_rawNearHodge (R+L) ((Metric.ball (0 : V12Spatial) L).indicator B) x‖ ≤
        (Real.pi * L)⁻¹ * ∫ y in {y : V12Spatial | L ≤ ‖y‖}, ‖B y‖ := by
  rw [v12_actualHodge_near_far R L x hx B hi, add_sub_cancel_left]
  exact (v12_hodge_far_integrable_and_bound R L hL hRL x hx B hB).2

#print axioms v12_rawNearHodge_eq_density_cutoff
#print axioms v12_actualHodge_near_far
#print axioms v12_actualHodge_near_error_bound
end SMScattering.W20Full
