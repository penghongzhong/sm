import lean.v12.V12_YVHodgeSpacetimeBudget
import lean.v12.V12_YWICurvatureNearError
import lean.v12.V12_YSCurvatureCutoffL1
import lean.v12.V12_YXYoungSpacetimeLimit

/-! The same-field near/far error is controlled on the actual finite
spacetime cylinder. Both HLS integrability hypotheses are proved from Q. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_HodgeApproxError (R L : ℝ)
    (qn q : V12Spacetime → V12Field) (z : V12Spacetime) : V12Spatial :=
  (v12_spacetimeHodge qn z - v12_spacetimeHodge q z) -
    v12_spacetimeNearHodge (R+L) (v12_curvatureCutoffDifference L qn q) z

theorem v12_HodgeApproxError_stronglyMeasurable
    (R L : ℝ) (qn q : V12Spacetime → V12Field)
    (hn : StronglyMeasurable qn) (hq : StronglyMeasurable q) :
    StronglyMeasurable (v12_HodgeApproxError R L qn q) :=
  ((v12_spacetimeHodge_stronglyMeasurable qn hn).sub
    (v12_spacetimeHodge_stronglyMeasurable q hq)).sub
      (v12_spacetimeNearHodge_stronglyMeasurable (R+L) _
        (v12_curvatureCutoffDifference_stronglyMeasurable L qn q hn hq))

theorem v12_HodgeApproxError_ae_bound
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (R : ℕ) (L : ℝ)
    (hL : 0 < L) (hRL : 2*((R : ℝ)+1) ≤ L)
    (qn q : V12Spacetime → V12Field)
    (hmn : StronglyMeasurable qn) (hmq : StronglyMeasurable q)
    (hn4 : MemLp qn 4 (v12_slab_measure a b)) (hq4 : MemLp q 4 (v12_slab_measure a b))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    ∀ᵐ z ∂(v12_slab_measure a b).restrict (v12_spatial_cylinder R),
      ‖v12_HodgeApproxError ((R : ℝ)+1) L qn q z‖ ≤ (Real.pi*L)⁻¹*(4*M^2) := by
  let μ := (volume : Measure ℝ).restrict (Set.Icc a b)
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_HLS hHLS
  rw [v12_cylinder_measure_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (v12_HodgeApproxError_stronglyMeasurable _ L qn q hmn hmq).measurable.norm measurable_const)).2
  filter_upwards [hEn, hEq,
    v12_spacetime_memLp_slices μ 4 (by norm_num) (by norm_num) qn hn4,
    v12_spacetime_memLp_slices μ 4 (by norm_num) (by norm_num) q hq4] with t hen heq hn4t hq4t
  have hn2 : MemLp (fun x => qn (t,x)) 2 (volume : Measure V12Spatial) :=
    hen.trans_lt ENNReal.ofReal_lt_top
  have hq2 : MemLp (fun x => q (t,x)) 2 (volume : Measure V12Spatial) :=
    heq.trans_lt ENNReal.ofReal_lt_top
  have hIn := (hH (fun x => v12_curvatureDensity (qn (t,x)))
    (v12_curvatureDensity_mixed_memLp volume _ hn2 hn4t)).1
  have hIq := (hH (fun x => v12_curvatureDensity (q (t,x)))
    (v12_curvatureDensity_mixed_memLp volume _ hq2 hq4t)).1
  filter_upwards [hIn.restrict (s := Metric.ball (0 : V12Spatial) ((R : ℝ)+1)),
    hIq.restrict (s := Metric.ball (0 : V12Spatial) ((R : ℝ)+1)),
    ae_restrict_mem (μ := (volume : Measure V12Spatial)) measurableSet_ball] with x hin hiq hx
  have hxx : ‖x‖ ≤ (R : ℝ)+1 := by
    exact (show ‖x‖ < (R : ℝ)+1 by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  have hb := v12_actual_curvature_near_error (fun y => qn (t,y)) (fun y => q (t,y))
    hn2 hq2 M hM hen heq ((R : ℝ)+1) L hL hRL x hxx hin hiq
  have hd : (fun y => v12_curvatureCutoffDifference L qn q (t,y)) =
      (Metric.ball (0 : V12Spatial) L).indicator
        (fun y => v12_curvatureDensity (qn (t,y)) - v12_curvatureDensity (q (t,y))) := by
    funext y
    simp only [v12_curvatureCutoffDifference, Set.indicator_apply,
      Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
  change ‖(v12_rawHodgePotential (fun y => v12_curvatureDensity (qn (t,y))) x -
    v12_rawHodgePotential (fun y => v12_curvatureDensity (q (t,y))) x) -
    v12_rawNearHodge (((R : ℝ)+1)+L) (fun y => v12_curvatureCutoffDifference L qn q (t,y)) x‖ ≤ _
  rw [hd]
  exact hb

theorem v12_HodgeApproxError_Lp_bound
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (R : ℕ) (L : ℝ)
    (hL : 0 < L) (hRL : 2*((R : ℝ)+1) ≤ L)
    (qn q : V12Spacetime → V12Field)
    (hmn : StronglyMeasurable qn) (hmq : StronglyMeasurable q)
    (hn4 : MemLp qn 4 (v12_slab_measure a b)) (hq4 : MemLp q 4 (v12_slab_measure a b))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (p : ℝ≥0∞) :
    let ν := (v12_slab_measure a b).restrict (v12_spatial_cylinder R)
    eLpNorm (v12_HodgeApproxError ((R : ℝ)+1) L qn q) p ν ≤
      (ν Set.univ)^p.toReal⁻¹ * ENNReal.ofReal ((Real.pi*L)⁻¹*(4*M^2)) := by
  exact eLpNorm_le_of_ae_bound
    (v12_HodgeApproxError_stronglyMeasurable _ L qn q hmn hmq).aestronglyMeasurable
    (v12_HodgeApproxError_ae_bound hHLS a b R L hL hRL qn q hmn hmq hn4 hq4 M hM hEn hEq)

#print axioms v12_HodgeApproxError_ae_bound
#print axioms v12_HodgeApproxError_Lp_bound
end SMScattering.W20Full
