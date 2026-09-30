import lean.v12.V12_YZZBTOriginalPotentialRepresentative
import lean.v12.V12_YRZZeroOrderAlgebra

/-! All three original source-coefficient budgets, derived from Q's energy
and spacetime L4 bounds and the explicitly stated original A0/V formulas.
No coefficient Lp membership or norm bound is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_smoothSlabExtension_energy
    (a b : ℝ) (q : V12Spacetime → V12Field) (M : ℝ)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => v12_smoothSlabExtension a b q (t,x)) 2 volume ≤ ENNReal.ofReal M := by
  filter_upwards [hE, ae_restrict_mem measurableSet_Icc] with t ht htI
  have he : (fun x => v12_smoothSlabExtension a b q (t,x)) = (fun x => q (t,x)) :=
    funext (fun x => v12_smoothSlabExtension_apply a b q t htI x)
  rw [he]
  exact ht

theorem v12_original_source_coefficient_budgets (hHLS : V12ExternalHLS2D) :
    ∃ CA : ℝ≥0∞, CA ≠ ∞ ∧ ∃ CV : ℝ, 0 ≤ CV ∧
    ∀ (a b : ℝ) (q : V12Spacetime → V12Field)
      (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
      (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ), 0 ≤ M →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) →
      ∀ (Z : ℝ≥0∞), Z ≠ ∞ → eLpNorm q 4 (v12_slab_measure a b) ≤ Z →
      ∀ (A0 V : V12Spacetime → ℂ),
      ContinuousOn A0 (Set.Icc a b ×ˢ Set.univ) →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        ∀ ht : MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial),
        (fun x => A0 (t,x)) =ᵐ[volume]
        (v12_temporalCoulombClass
          (fun j k => v12_SL2Class volume j k (fun x => q (t,x)) ht)
          (v12_massComplexL2Class volume (fun x => q (t,x)) ht) : V12Spatial → ℂ)) →
      (∀ z, V z = -A0 z + ((‖v12_spacetimeHodge q z‖^2 : ℝ) : ℂ) -
        (2 : ℂ) * ((‖q z‖^2 : ℝ) : ℂ)) →
      (∀ j, MemLp (v12_actualCoulombA q j) 4 (v12_slab_measure a b) ∧
        eLpNorm (v12_actualCoulombA q j) 4 (v12_slab_measure a b) ≤ CA*ENNReal.ofReal M*Z) ∧
      (MemLp V 2 (v12_slab_measure a b) ∧
        eLpNorm V 2 (v12_slab_measure a b) ≤ ENNReal.ofReal ((24+CV*M^2)*Z.toReal^2)) ∧
      (MemLp (fun z => v12_WDensity (q z)) 2 (v12_slab_measure a b) ∧
        eLpNorm (fun z => v12_WDensity (q z)) 2 (v12_slab_measure a b) ≤ 2*Z^2) := by
  obtain ⟨CA, hCA, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  obtain ⟨CV, hCV, hVb⟩ := v12_actualPotential_L2_budget hHLS
  refine ⟨CA, hCA, CV, hCV, ?_⟩
  intro a b q hc hq M hM hE Z hZ hb A0 V hc0 hformula hV
  let ext := v12_smoothSlabExtension a b q
  have hm := v12_smoothSlabExtension_stronglyMeasurable a b q hc
  have h4 := v12_smoothSlabExtension_memLp a b q 4 hq
  have hEe := v12_smoothSlabExtension_energy a b q M hE
  have hbe : eLpNorm ext 4 (v12_slab_measure a b) ≤ Z := by
    rw [v12_smoothSlabExtension_eLpNorm]
    exact hb
  obtain ⟨hH4, hHb⟩ := hH a b ext hm h4 (ENNReal.ofReal M) (by finiteness) hEe
  have hAeq (j : Fin 2) : v12_actualCoulombA ext j =ᵐ[v12_slab_measure a b]
      v12_actualCoulombA q j := by
    filter_upwards [v12_smoothSlabExtension_Hodge_ae a b q] with z hz
    simp only [v12_actualCoulombA, hz]
  have hAs (j : Fin 2) : MemLp (v12_actualCoulombA q j) 4 (v12_slab_measure a b) ∧
      eLpNorm (v12_actualCoulombA q j) 4 (v12_slab_measure a b) ≤ CA*ENNReal.ofReal M*Z := by
    have hcomp := v12_actualCoulombA_eLpNorm_le (v12_slab_measure a b) ext hm 4 j
    have he := eLpNorm_congr_ae (hAeq j) (p := (4 : ℝ≥0∞))
    refine ⟨?_, ?_⟩
    · change eLpNorm (v12_actualCoulombA q j) 4 (v12_slab_measure a b) < ∞
      rw [← he]
      exact hcomp.trans_lt hH4
    · rw [← he]
      exact (hcomp.trans hHb).trans (mul_le_mul' le_rfl hbe)
  have ha0 := v12_original_A0_joint_representative a b q hq A0 hc0 hformula
  have hv := v12_original_V_extended_representative hHLS a b q hc hq M hEe A0 V ha0 hV
  have hv4 := v12_original_V_memLp_of_representative (v12_slab_measure a b) V _ hv
  have hvb := v12_original_V_budget_of_representative (v12_slab_measure a b) V _ hv
    ((24+CV*M^2)*Z.toReal^2) (hVb a b ext hm h4 M hM hEe Z hZ hbe)
  have hnonneg : 0 ≤ (24+CV*M^2)*Z.toReal^2 :=
    mul_nonneg (add_nonneg (by norm_num) (mul_nonneg hCV (sq_nonneg M))) (sq_nonneg _)
  have hW := v12_actual_W_mass_L2_budgets (v12_slab_measure a b) q hq
  refine ⟨hAs, ⟨hv4, (ENNReal.le_ofReal_iff_toReal_le hv4.eLpNorm_ne_top hnonneg).mpr hvb⟩,
    hW.1, ?_⟩
  exact hW.2.2.1.trans (mul_le_mul' le_rfl (pow_le_pow_left' hb 2))

#print axioms v12_smoothSlabExtension_energy
#print axioms v12_original_source_coefficient_budgets
end SMScattering.W20Full
