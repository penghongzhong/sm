import lean.v12.V12_YSZZSpacetimeReality
import lean.v12.V12_YZZBActualPotentialWeak

/-! Exact raw representative and reality of the reconstructed V. This
identifies the L2 coefficient used in compact testing with the original
-A0+|A|^2-2m formula, rather than an independently chosen weak limit. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_actualPotentialL2Class_ae
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hmq : StronglyMeasurable q) (hq4 : MemLp q 4 ((((volume : Measure ℝ).restrict (Set.Icc a b)).prod (volume : Measure V12Spatial)))) (M : ℝ)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    (v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq : V12Spacetime → ℂ) =ᵐ[(((volume : Measure ℝ).restrict (Set.Icc a b)).prod (volume : Measure V12Spatial))]
      fun z => -v12_actualTemporalCoulombL2 a b q hq4 z +
        ((‖v12_spacetimeHodge q z‖^2 : ℝ) : ℂ) - (2 : ℂ) * ((‖q z‖^2 : ℝ) : ℂ) := by
  let μ := (((volume : Measure ℝ).restrict (Set.Icc a b)).prod (volume : Measure V12Spatial))
  let A0 := v12_actualTemporalCoulombL2 a b q hq4
  let H := v12_normSqL2Class μ (v12_spacetimeHodge q)
    (v12_actual_Hodge_memLp4 hHLS a b q hmq hq4 M hEq)
  let m := v12_massComplexL2Class μ q hq4
  have hH := (v12_normSq_memLp_two μ (v12_spacetimeHodge q)
    (v12_actual_Hodge_memLp4 hHLS a b q hmq hq4 M hEq)).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (-A0+H) ((2 : ℂ) • m), Lp.coeFn_add (-A0) H,
    Lp.coeFn_neg A0, Lp.coeFn_smul (2 : ℂ) m, hH, v12_massComplexL2Class_ae μ q hq4]
    with z hsub hadd hneg hsm hh hm
  change v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq z = (-A0+H) z - ((2 : ℂ) • m) z at hsub
  change H z = ((‖v12_spacetimeHodge q z‖^2 : ℝ) : ℂ) at hh
  change m z = ((‖q z‖^2 : ℝ) : ℂ) at hm
  rw [hsub, hadd, Pi.add_apply, hneg, Pi.neg_apply, hsm, Pi.smul_apply, smul_eq_mul, hh, hm]

theorem v12_actualPotentialL2Class_real
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hmq : StronglyMeasurable q) (hq4 : MemLp q 4 ((((volume : Measure ℝ).restrict (Set.Icc a b)).prod (volume : Measure V12Spatial)))) (M : ℝ)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    v12_LpIsReal ((((volume : Measure ℝ).restrict (Set.Icc a b)).prod (volume : Measure V12Spatial))) (v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq) := by
  filter_upwards [v12_actualPotentialL2Class_ae hHLS a b q hmq hq4 M hEq,
    v12_actualTemporalCoulomb_real a b q hq4] with z hz ha
  rw [hz]
  simp only [star_sub, star_add, star_neg, star_mul, ha, Complex.star_def, Complex.conj_ofReal]
  all_goals norm_num

#print axioms v12_actualPotentialL2Class_ae
#print axioms v12_actualPotentialL2Class_real
end SMScattering.W20Full
