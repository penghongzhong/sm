import lean.v12.V12_FrequencyTightnessLimit
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! The auxiliary compact test cutoff is constructed, not an assumption. -/
set_option autoImplicit false
namespace SMScattering.W20Full

theorem v12_exists_compact_test_cutoff :
    ∃ χ : SchwartzMap V12Spatial ℝ,
      HasCompactSupport χ ∧ χ 0 = 1 ∧ ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := by
  let c : ContDiffBump (0 : V12Spatial) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨c.hasCompactSupport.toSchwartzMap c.contDiff, c.hasCompactSupport, ?_, ?_⟩
  · exact c.one_of_mem_closedBall (Metric.mem_closedBall_self c.rIn_pos.le)
  · intro y
    exact ⟨c.nonneg, c.le_one⟩

#print axioms v12_exists_compact_test_cutoff
end SMScattering.W20Full
