import lean.v12.V12_SourceProducts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
Strong measurability of actual Lp-valued sections is derived from a jointly
measurable raw field and exact representatives. Distances to fixed Lp points
are parameter integrals; second countability then gives Borel measurability.
This does not assume Bochner measurability as an interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open MeasureTheory
open scoped ENNReal

theorem v12_measurable_of_dist_to_points
    {α E : Type*} [MeasurableSpace α] [MetricSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (f : α → E) (hd : ∀ x : E, Measurable (fun a => dist (f a) x)) :
    Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  choose r hr hsub using fun x : U => Metric.isOpen_iff.mp hU x.val x.property
  have hcover : (⋃ x : U, Metric.ball x.val (r x)) = U := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun x => hsub x)
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩, Metric.mem_ball_self (hr ⟨x,hx⟩)⟩
  obtain ⟨T, hTcount, hT⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x : U => Metric.ball x.val (r x)) (fun _ => Metric.isOpen_ball)
  rw [← hcover, ← hT]
  simp only [Set.preimage_iUnion]
  apply MeasurableSet.biUnion hTcount
  intro x _
  exact measurableSet_lt (hd x.val) measurable_const

/-- No regularity or measurability of the Lp-valued map is assumed. -/
theorem v12_stronglyMeasurable_Lp_sections
    (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → V12Field) (hq : Measurable q)
    (Q : ℝ → Lp V12Field p (volume : Measure V12Spatial))
    (hrep : ∀ t, (Q t : V12Spatial → V12Field) =ᵐ[volume] fun y => q (t,y)) :
    StronglyMeasurable Q := by
  borelize (Lp V12Field p (volume : Measure V12Spatial) : Type)
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hptop : p ≠ ∞ := Fact.out
  apply Measurable.stronglyMeasurable
  apply v12_measurable_of_dist_to_points
  intro f
  let hm := Lp.aestronglyMeasurable f
  let fraw := hm.mk (f : V12Spatial → V12Field)
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
  have heq : (fun y => (Q t : V12Spatial → V12Field) y - f y)
      =ᵐ[volume] fun y => q (t,y) - fraw y := by
    filter_upwards [hrep t, hm.ae_eq_mk] with y hqy hfy
    rw [hqy, hfy]
  rw [Lp.dist_def, eLpNorm_congr_ae heq]
  have hsection : AEStronglyMeasurable (fun y => q (t,y) - fraw y)
      (volume : Measure V12Spatial) :=
    (hD.comp measurable_prodMk_left).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hsection]

/-- A measurable full-measure set handles exceptional time slices exactly. -/
theorem v12_aestronglyMeasurable_Lp_sections_of_measurable
    (μ : Measure ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → V12Field) (hq : Measurable q)
    (Q : ℝ → Lp V12Field p (volume : Measure V12Spatial))
    (hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → V12Field) =ᵐ[volume] fun y => q (t,y)) :
    AEStronglyMeasurable Q μ := by
  classical
  obtain ⟨s, hsfull, hsmeas, hsrep⟩ := hrep.exists_measurable_mem
  let q' : ℝ × V12Spatial → V12Field := (Prod.fst ⁻¹' s).indicator q
  let Q' : ℝ → Lp V12Field p (volume : Measure V12Spatial) := s.indicator Q
  have hq' : Measurable q' := hq.indicator (hsmeas.preimage measurable_fst)
  have hrep' : ∀ t, (Q' t : V12Spatial → V12Field) =ᵐ[volume] fun y => q' (t,y) := by
    intro t
    by_cases ht : t ∈ s
    · change ((s.indicator Q) t : V12Spatial → V12Field) =ᵐ[volume] _
      rw [Set.indicator_of_mem ht]
      filter_upwards [hsrep t ht] with y hy
      change (Q t : V12Spatial → V12Field) y = (Prod.fst ⁻¹' s).indicator q (t,y)
      rw [Set.indicator_of_mem (show (t,y) ∈ Prod.fst ⁻¹' s from ht)]
      exact hy
    · change ((s.indicator Q) t : V12Spatial → V12Field) =ᵐ[volume] _
      rw [Set.indicator_of_notMem ht]
      filter_upwards [Lp.coeFn_zero (E := V12Field) (p := p)
        (μ := (volume : Measure V12Spatial))] with y hy
      change (0 : Lp V12Field p (volume : Measure V12Spatial)) y =
        (Prod.fst ⁻¹' s).indicator q (t,y)
      rw [Set.indicator_of_notMem (show (t,y) ∉ Prod.fst ⁻¹' s from ht)]
      exact hy
  have hstrong := v12_stronglyMeasurable_Lp_sections p q' hq' Q' hrep'
  apply hstrong.aestronglyMeasurable.congr
  filter_upwards [hsfull] with t ht
  exact Set.indicator_of_mem ht Q

/-- Joint a.e. measurability suffices; no measurable Lp-valued map is assumed. -/
theorem v12_aestronglyMeasurable_Lp_sections
    (μ : Measure ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → V12Field)
    (hq : AEStronglyMeasurable q (μ.prod (volume : Measure V12Spatial)))
    (Q : ℝ → Lp V12Field p (volume : Measure V12Spatial))
    (hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → V12Field) =ᵐ[volume] fun y => q (t,y)) :
    AEStronglyMeasurable Q μ := by
  apply v12_aestronglyMeasurable_Lp_sections_of_measurable μ p (hq.mk q)
    hq.stronglyMeasurable_mk.measurable Q
  filter_upwards [hrep, Measure.ae_ae_of_ae_prod hq.ae_eq_mk] with t ht hmk
  exact ht.trans hmk

#print axioms v12_aestronglyMeasurable_Lp_sections_of_measurable
#print axioms v12_aestronglyMeasurable_Lp_sections

#print axioms v12_measurable_of_dist_to_points
#print axioms v12_stronglyMeasurable_Lp_sections

end SMScattering.W20Full
