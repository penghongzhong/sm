import lean.v12.V12_YMeasurableLpSections
import lean.v12.V12_YSpacetimeSlices

/-!
Exact Fubini norm identification for the SAME raw spacetime field and its
Lp-valued sections. Bochner measurability is proved in the preceding module,
not assumed. The resulting norm equality transfers the actual source bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open MeasureTheory
open scoped ENNReal

theorem v12_eLpNorm_sections_eq_spacetime
    (μ : Measure ℝ) [SFinite μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → V12Field)
    (hq : AEStronglyMeasurable q (μ.prod (volume : Measure V12Spatial)))
    (Q : ℝ → Lp V12Field p (volume : Measure V12Spatial))
    (hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → V12Field) =ᵐ[volume] fun y => q (t,y)) :
    eLpNorm Q p μ = eLpNorm q p (μ.prod (volume : Measure V12Spatial)) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hptop : p ≠ ∞ := Fact.out
  have hpr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hptop).ne'
  have hQ := v12_aestronglyMeasurable_Lp_sections μ p q hq Q hrep
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hQ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hq,
    lintegral_prod _ (hq.enorm.aemeasurable.pow_const p.toReal)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hrep] with t ht
  have hslice : AEStronglyMeasurable (fun y => q (t,y)) (volume : Measure V12Spatial) :=
    (Lp.aestronglyMeasurable (Q t)).congr ht
  rw [Lp.enorm_def, eLpNorm_congr_ae ht,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hslice,
    ← ENNReal.rpow_mul, one_div_mul_cancel hpr, ENNReal.rpow_one]

/-- The time-space Lp conclusion and its exact norm are constructed. -/
theorem v12_exists_Bochner_Lp_sections
    (μ : Measure ℝ) [SFinite μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (q : ℝ × V12Spatial → V12Field)
    (hq : MemLp q p (μ.prod (volume : Measure V12Spatial))) :
    ∃ Q : ℝ → Lp V12Field p (volume : Measure V12Spatial),
      (∀ᵐ t ∂μ, (Q t : V12Spatial → V12Field) =ᵐ[volume] fun y => q (t,y)) ∧
      MemLp Q p μ ∧ eLpNorm Q p μ = eLpNorm q p (μ.prod (volume : Measure V12Spatial)) := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hptop : p ≠ ∞ := Fact.out
  let Q : ℝ → Lp V12Field p (volume : Measure V12Spatial) := fun t =>
    if h : MemLp (fun y => q (t,y)) p (volume : Measure V12Spatial)
    then h.toLp (fun y => q (t,y)) else 0
  have hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → V12Field) =ᵐ[volume] fun y => q (t,y) := by
    filter_upwards [v12_spacetime_memLp_slices μ p hp0 hptop q hq] with t ht
    simp only [Q, dif_pos ht]
    exact ht.coeFn_toLp
  have hnorm := v12_eLpNorm_sections_eq_spacetime μ p q hq.aestronglyMeasurable Q hrep
  refine ⟨Q, hrep, ?_, hnorm⟩
  exact hnorm.trans_lt hq

/-- Actual nonlinear source classes and time-Lp bounds, from raw spacetime bounds. -/
theorem v12_exists_actual_source_Bochner_realizations
    (μ : Measure ℝ) [SFinite μ]
    (A : Fin 2 → V12Spacetime → ℂ) (V W : V12Spacetime → ℂ)
    (q : V12Spacetime → V12Field)
    (hA : ∀ j, MemLp (A j) 4 (μ.prod (volume : Measure V12Spatial)))
    (hV : MemLp V 2 (μ.prod (volume : Measure V12Spatial)))
    (hW : MemLp W 2 (μ.prod (volume : Measure V12Spatial)))
    (hq : MemLp q 4 (μ.prod (volume : Measure V12Spatial))) :
    ∃ (F : Fin 2 → ℝ → V12SpatialL2) (G : ℝ → V12SpatialLFourThirds),
      (∀ j, ∀ᵐ t ∂μ, (F j t : V12Spatial → V12Field)
        =ᵐ[volume] fun y => v12_driftProduct A q j (t,y)) ∧
      (∀ᵐ t ∂μ, (G t : V12Spatial → V12Field)
        =ᵐ[volume] fun y => v12_zeroOrderProduct V W q (t,y)) ∧
      (∀ j, MemLp (F j) 2 μ) ∧ MemLp G ((4 : ℝ≥0∞) / 3) μ ∧
      (∀ j, eLpNorm (F j) 2 μ ≤
        eLpNorm (A j) 4 (μ.prod (volume : Measure V12Spatial)) *
          eLpNorm q 4 (μ.prod (volume : Measure V12Spatial))) ∧
      eLpNorm G ((4 : ℝ≥0∞) / 3) μ ≤
        (eLpNorm V 2 (μ.prod (volume : Measure V12Spatial)) +
          eLpNorm W 2 (μ.prod (volume : Measure V12Spatial))) *
        eLpNorm q 4 (μ.prod (volume : Measure V12Spatial)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : Fact (((4 : ℝ≥0∞) / 3) ≠ ∞) := ⟨by norm_num⟩
  have hFex := fun j => v12_exists_Bochner_Lp_sections μ 2 (v12_driftProduct A q j)
    (v12_driftProduct_memLp (μ.prod (volume : Measure V12Spatial)) A q j (hA j) hq)
  choose F hFr hFLp hFnorm using hFex
  obtain ⟨G, hGr, hGLp, hGnorm⟩ :=
    v12_exists_Bochner_Lp_sections μ ((4 : ℝ≥0∞) / 3) (v12_zeroOrderProduct V W q)
      (v12_zeroOrderProduct_memLp (μ.prod (volume : Measure V12Spatial)) V W q hV hW hq)
  refine ⟨F, G, hFr, hGr, hFLp, hGLp, ?_, ?_⟩
  · intro j
    rw [hFnorm j]
    exact v12_driftProduct_eLpNorm_le (μ.prod (volume : Measure V12Spatial)) A q j
      (hA j).aestronglyMeasurable hq.aestronglyMeasurable
  · rw [hGnorm]
    exact v12_zeroOrderProduct_eLpNorm_le (μ.prod (volume : Measure V12Spatial)) V W q
      hV.aestronglyMeasurable hW.aestronglyMeasurable hq.aestronglyMeasurable

#print axioms v12_exists_actual_source_Bochner_realizations

#print axioms v12_eLpNorm_sections_eq_spacetime
#print axioms v12_exists_Bochner_Lp_sections

end SMScattering.W20Full
