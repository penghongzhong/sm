import lean.v12.V12_YSCurvatureMixedBounds
import lean.v12.V12_YTHodgeHLSApplication

/-! Apply HLS to the actual curvature, deriving the spatial energy/L4
Hodge estimate. The only external input is the registered scalar HLS theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_actual_hodge_energy_L4_bound (hHLS : V12ExternalHLS2D) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : V12Spatial → V12Field,
      MemLp q 2 (volume : Measure V12Spatial) → MemLp q 4 (volume : Measure V12Spatial) →
      MemLp (v12_rawHodgePotential (fun x => v12_curvatureDensity (q x))) 4 volume ∧
      eLpNorm (v12_rawHodgePotential (fun x => v12_curvatureDensity (q x))) 4 volume ≤
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * C) *
          (2 * (eLpNorm q 2 volume * eLpNorm q 4 volume)) := by
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_HLS hHLS
  refine ⟨C, hC, ?_⟩
  intro q h2 h4
  have hB := v12_curvatureDensity_mixed_memLp volume q h2 h4
  obtain ⟨hi, hA, hn⟩ := hH (fun x => v12_curvatureDensity (q x)) hB
  refine ⟨hA, hn.trans ?_⟩
  exact mul_le_mul' le_rfl (v12_curvatureDensity_mixed_bound volume q h2.aestronglyMeasurable)

#print axioms v12_actual_hodge_energy_L4_bound
end SMScattering.W20Full
