import lean.v12.V12_YMeasurableLpSections

/-! Scalar and spatial-vector versions of the already checked section
construction. Needed for the same raw Hodge fields, not assumed time maps. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/-- No regularity or measurability of the Lp-valued map is assumed. -/
theorem v12_generic_stronglyMeasurable_Lp_sections
    (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → E) (hq : Measurable q)
    (Q : ℝ → Lp E p (volume : Measure V12Spatial))
    (hrep : ∀ t, (Q t : V12Spatial → E) =ᵐ[volume] fun y => q (t,y)) :
    StronglyMeasurable Q := by
  borelize (Lp E p (volume : Measure V12Spatial) : Type*)
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hptop : p ≠ ∞ := Fact.out
  apply Measurable.stronglyMeasurable
  apply v12_measurable_of_dist_to_points
  intro f
  let hm := Lp.aestronglyMeasurable f
  let fraw := hm.mk (f : V12Spatial → E)
  have hfraw : Measurable fraw := hm.stronglyMeasurable_mk.measurable
  have hD : Measurable (fun z : ℝ × V12Spatial => q z - fraw z.2) :=
    hq.sub (hfraw.comp measurable_snd)
  have hK : Measurable (fun z : ℝ × V12Spatial => ‖q z - fraw z.2‖ₑ ^ p.toReal) := by
    fun_prop
  have hInt := hK.lintegral_prod_right' (ν := (volume : Measure V12Spatial))
  have hmeas : Measurable (fun t : ℝ =>
      ((∫⁻ y : V12Spatial, ‖q (t,y) - fraw y‖ₑ ^ p.toReal) ^ (1 / p.toReal)).toReal) := by
    fun_prop
  convert hmeas using 1
  funext t
  have heq : (fun y => (Q t : V12Spatial → E) y - f y)
      =ᵐ[volume] fun y => q (t,y) - fraw y := by
    filter_upwards [hrep t, hm.ae_eq_mk] with y hqy hfy
    rw [hqy, hfy]
  rw [Lp.dist_def]
  change (eLpNorm (fun y => (Q t : V12Spatial → E) y - f y) p volume).toReal = _
  rw [eLpNorm_congr_ae heq]
  have hsection : AEStronglyMeasurable (fun y => q (t,y) - fraw y)
      (volume : Measure V12Spatial) :=
    (hD.comp measurable_prodMk_left).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hsection]

/-- A measurable full-measure set handles exceptional time slices exactly. -/
theorem v12_generic_aestronglyMeasurable_Lp_sections_of_measurable
    (μ : Measure ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → E) (hq : Measurable q)
    (Q : ℝ → Lp E p (volume : Measure V12Spatial))
    (hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → E) =ᵐ[volume] fun y => q (t,y)) :
    AEStronglyMeasurable Q μ := by
  classical
  obtain ⟨s, hsfull, hsmeas, hsrep⟩ := hrep.exists_measurable_mem
  let q' : ℝ × V12Spatial → E := (Prod.fst ⁻¹' s).indicator q
  let Q' : ℝ → Lp E p (volume : Measure V12Spatial) := s.indicator Q
  have hq' : Measurable q' := hq.indicator (hsmeas.preimage measurable_fst)
  have hrep' : ∀ t, (Q' t : V12Spatial → E) =ᵐ[volume] fun y => q' (t,y) := by
    intro t
    by_cases ht : t ∈ s
    · change ((s.indicator Q) t : V12Spatial → E) =ᵐ[volume] _
      rw [Set.indicator_of_mem ht]
      filter_upwards [hsrep t ht] with y hy
      change (Q t : V12Spatial → E) y = (Prod.fst ⁻¹' s).indicator q (t,y)
      rw [Set.indicator_of_mem (show (t,y) ∈ Prod.fst ⁻¹' s from ht)]
      exact hy
    · change ((s.indicator Q) t : V12Spatial → E) =ᵐ[volume] _
      rw [Set.indicator_of_notMem ht]
      filter_upwards [Lp.coeFn_zero (E := E) (p := p)
        (μ := (volume : Measure V12Spatial))] with y hy
      change (0 : Lp E p (volume : Measure V12Spatial)) y =
        (Prod.fst ⁻¹' s).indicator q (t,y)
      rw [Set.indicator_of_notMem (show (t,y) ∉ Prod.fst ⁻¹' s from ht)]
      exact hy
  have hstrong := v12_generic_stronglyMeasurable_Lp_sections p q' hq' Q' hrep'
  apply hstrong.aestronglyMeasurable.congr
  filter_upwards [hsfull] with t ht
  exact Set.indicator_of_mem ht Q

/-- Joint a.e. measurability suffices; no measurable Lp-valued map is assumed. -/
theorem v12_generic_aestronglyMeasurable_Lp_sections
    (μ : Measure ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → E)
    (hq : AEStronglyMeasurable q (μ.prod (volume : Measure V12Spatial)))
    (Q : ℝ → Lp E p (volume : Measure V12Spatial))
    (hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → E) =ᵐ[volume] fun y => q (t,y)) :
    AEStronglyMeasurable Q μ := by
  apply v12_generic_aestronglyMeasurable_Lp_sections_of_measurable μ p (hq.mk q)
    hq.stronglyMeasurable_mk.measurable Q
  filter_upwards [hrep, Measure.ae_ae_of_ae_prod hq.ae_eq_mk] with t ht hmk
  exact ht.trans hmk

theorem v12_generic_eLpNorm_sections_eq_spacetime
    (μ : Measure ℝ) [SFinite μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → E)
    (hq : AEStronglyMeasurable q (μ.prod (volume : Measure V12Spatial)))
    (Q : ℝ → Lp E p (volume : Measure V12Spatial))
    (hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → E) =ᵐ[volume] fun y => q (t,y)) :
    eLpNorm Q p μ = eLpNorm q p (μ.prod (volume : Measure V12Spatial)) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hptop : p ≠ ∞ := Fact.out
  have hpr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hptop).ne'
  have hQ := v12_generic_aestronglyMeasurable_Lp_sections μ p q hq Q hrep
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hQ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hq,
    lintegral_prod _ (hq.enorm.pow_const p.toReal)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hrep] with t ht
  have hslice : AEStronglyMeasurable (fun y => q (t,y)) (volume : Measure V12Spatial) :=
    (Lp.aestronglyMeasurable (Q t)).congr ht
  rw [Lp.enorm_def, eLpNorm_congr_ae ht,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hslice,
    ← ENNReal.rpow_mul, one_div_mul_cancel hpr, ENNReal.rpow_one]


#print axioms v12_generic_aestronglyMeasurable_Lp_sections
#print axioms v12_generic_eLpNorm_sections_eq_spacetime
end SMScattering.W20Full
