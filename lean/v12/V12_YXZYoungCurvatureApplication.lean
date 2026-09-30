import lean.v12.V12_YSCurvatureCutoffL1
import lean.v12.V12_YXYoungSpacetimeLimit

/-! Apply the actual Young spacetime convergence theorem to the original
curvature difference. No density convergence/budget is a new premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_curvature_near_spacetime_limit
    (a b : ℝ) (R : ℕ) (K : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hmn : ∀ n, StronglyMeasurable (qn n)) (hmq : StronglyMeasurable q)
    (hn : ∀ n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq : MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    (∀ n, MemLp (v12_spacetimeNearHodge K
      (v12_curvatureCutoffDifference ((R : ℝ)+1) (qn n) q)) ((4 : ℝ≥0∞) / 3)
      (v12_slab_measure a b)) ∧
    Tendsto (fun n => (eLpNorm (v12_spacetimeNearHodge K
      (v12_curvatureCutoffDifference ((R : ℝ)+1) (qn n) q)) ((4 : ℝ≥0∞) / 3)
      (v12_slab_measure a b)).toReal) atTop (𝓝 0) := by
  obtain ⟨hi, ht⟩ := v12_curvatureCutoffDifference_L1_limit a b R qn q hn hq hlim
  apply (v12_actual_nearHodge_spacetime_limit
    ((volume : Measure ℝ).restrict (Set.Icc a b)) K
    (fun n => v12_curvatureCutoffDifference ((R : ℝ)+1) (qn n) q)
    (fun n => v12_curvatureCutoffDifference_stronglyMeasurable _ _ _ (hmn n) hmq)
    hi (4*M^2) (by positivity) ?_ ht)
  intro n
  filter_upwards [hEn n, hEq] with t htN htQ
  have hn2 : MemLp (fun x => qn n (t,x)) 2 (volume : Measure V12Spatial) :=
    htN.trans_lt ENNReal.ofReal_lt_top
  have hq2 : MemLp (fun x => q (t,x)) 2 (volume : Measure V12Spatial) :=
    htQ.trans_lt ENNReal.ofReal_lt_top
  convert v12_curvature_difference_cutoff_energy ((R : ℝ)+1)
    (fun x => qn n (t,x)) (fun x => q (t,x)) hn2 hq2 M hM htN htQ using 1
  congr 1
  funext y
  by_cases hy : ‖y‖ < (R : ℝ)+1 <;>
    simp [v12_curvatureCutoffDifference, Set.indicator_apply,
      Metric.mem_ball, dist_zero_right, hy]

#print axioms v12_actual_curvature_near_spacetime_limit
end SMScattering.W20Full
