import lean.v12.V12_YEveryTimeEnergy
import lean.v12.V12_YMeasurableLpSections

/-!
The same every-time energy representative is Bochner measurable. Fatou gives
all-time spatial bounds, while joint raw measurability proves L2-valued time
measurability. No a.e.-to-everywhere or Bochner conversion is assumed.
-/

set_option autoImplicit false

namespace SMScattering.W20Full

open MeasureTheory
open scoped ENNReal

theorem v12_exists_every_time_Bochner_L2_realization
    (a b : ℝ) (hab : a < b) (q : ℝ → V12Spatial → V12Field)
    (M : ℝ) (hM : 0 ≤ M)
    (hmeas : ∀ t ∈ Set.Icc a b,
      AEStronglyMeasurable (q t) (volume : Measure V12Spatial))
    (htime : ∀ x : V12Spatial, ContinuousOn (fun t => q t x) (Set.Icc a b))
    (hjoint : AEStronglyMeasurable (Function.uncurry q)
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod (volume : Measure V12Spatial)))
    (hbound : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (q t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M) :
    ∃ Q : ℝ → V12SpatialL2,
      (∀ t ∈ Set.Icc a b,
        ((Q t : V12Spatial → V12Field) =ᵐ[volume] q t) ∧ ‖Q t‖ ≤ M) ∧
      MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
      eLpNorm Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ ENNReal.ofReal M := by
  obtain ⟨Q, hQ⟩ := v12_exists_every_time_L2_realization a b hab q M hM hmeas htime hbound
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hrep : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (Q t : V12Spatial → V12Field) =ᵐ[volume] fun y => Function.uncurry q (t,y) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hQ t ht).1
  have hQM := v12_aestronglyMeasurable_Lp_sections
    ((volume : Measure ℝ).restrict (Set.Icc a b)) 2 (Function.uncurry q) hjoint Q hrep
  have hnorm : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b), ‖Q t‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hQ t ht).2
  refine ⟨Q, hQ, memLp_top_of_bound hQM M hnorm, ?_⟩
  rw [eLpNorm_exponent_top hQM]
  exact eLpNormEssSup_le_of_ae_bound hnorm

#print axioms v12_exists_every_time_Bochner_L2_realization

end SMScattering.W20Full
