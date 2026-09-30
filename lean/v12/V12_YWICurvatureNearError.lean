import lean.v12.V12_YWHodgeNearFarIdentity
import lean.v12.V12_YSActualHodgeFarBounds

/-! Quantitative near-approximation error for the same two original fields,
with the density tail budget derived from their energy. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_actual_curvature_near_error
    (qn q : V12Spatial → V12Field)
    (hn : MemLp qn 2 (volume : Measure V12Spatial)) (hq : MemLp q 2 (volume : Measure V12Spatial))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : eLpNorm qn 2 volume ≤ ENNReal.ofReal M) (hEq : eLpNorm q 2 volume ≤ ENNReal.ofReal M)
    (R L : ℝ) (hL : 0 < L) (hRL : 2*R ≤ L)
    (x : V12Spatial) (hx : ‖x‖ ≤ R)
    (hin : Integrable (fun y => v12_curvatureDensity (qn y) • v12_hodgeKernel (x-y)) volume)
    (hiq : Integrable (fun y => v12_curvatureDensity (q y) • v12_hodgeKernel (x-y)) volume) :
    ‖(v12_rawHodgePotential (fun y => v12_curvatureDensity (qn y)) x -
      v12_rawHodgePotential (fun y => v12_curvatureDensity (q y)) x) -
      v12_rawNearHodge (R+L) ((Metric.ball (0 : V12Spatial) L).indicator
        (fun y => v12_curvatureDensity (qn y) - v12_curvatureDensity (q y))) x‖ ≤
      (Real.pi * L)⁻¹ * (4*M^2) := by
  let Bn := fun y => v12_curvatureDensity (qn y)
  let B := fun y => v12_curvatureDensity (q y)
  obtain ⟨hBn, hnB⟩ := v12_actual_curvature_integral_bound qn hn M hM hEn
  obtain ⟨hB, hqB⟩ := v12_actual_curvature_integral_bound q hq M hM hEq
  have hid : Integrable (fun y => (Bn y - B y) • v12_hodgeKernel (x-y)) volume := by
    simpa only [Pi.sub_apply, sub_smul, Bn, B] using hin.sub hiq
  have he : v12_rawHodgePotential (fun y => Bn y - B y) x =
      v12_rawHodgePotential Bn x - v12_rawHodgePotential B x := by
    unfold v12_rawHodgePotential
    simp only [sub_smul]
    exact integral_sub hin hiq
  have hb := v12_actualHodge_near_error_bound R L hL hRL x hx (fun y => Bn y - B y)
    (hBn.sub hB) hid
  rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∫ y in {y : V12Spatial | L ≤ ‖y‖}, ‖Bn y - B y‖) ≤ ∫ y, ‖Bn y - B y‖ :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun y => norm_nonneg _)) (hBn.sub hB).norm
    _ ≤ ∫ y, ‖Bn y‖ + ‖B y‖ := integral_mono (hBn.sub hB).norm
      (hBn.norm.add hB.norm) (fun y => norm_sub_le _ _)
    _ = (∫ y, ‖Bn y‖) + (∫ y, ‖B y‖) := integral_add hBn.norm hB.norm
    _ ≤ 4*M^2 := by dsimp [Bn, B] at *; linarith

#print axioms v12_actual_curvature_near_error
end SMScattering.W20Full
