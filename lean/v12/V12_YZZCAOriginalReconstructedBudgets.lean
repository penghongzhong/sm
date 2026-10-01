import lean.v12.V12_YZZBZRawPotentialFormula

/-! Uniform original reconstructed A,V,W budgets from the same closed-slab
field's M,Z controls. In contrast with the historical smooth-representative
lemma, no A0 continuity or separately chosen potential representative is
required. Actual formula/extension applicability is proved. Pending CI. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_reconstructed_coefficient_budgets (hHLS : V12ExternalHLS2D) :
    ∃ CA : ℝ≥0∞, CA ≠ ∞ ∧ ∃ CV : ℝ, 0 ≤ CV ∧
    ∀ (a b : ℝ) (q : V12Spacetime → V12Field)
      (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
      (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ), 0 ≤ M →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) →
      ∀ (Z : ℝ≥0∞), Z ≠ ∞ → eLpNorm q 4 (v12_slab_measure a b) ≤ Z →
      (∀ j, MemLp (v12_actualCoulombA q j) 4 (v12_slab_measure a b) ∧
        eLpNorm (v12_actualCoulombA q j) 4 (v12_slab_measure a b) ≤ CA*ENNReal.ofReal M*Z) ∧
      (MemLp (v12_originalReconstructedPotential a b q hq) 2 (v12_slab_measure a b) ∧
        eLpNorm (v12_originalReconstructedPotential a b q hq) 2 (v12_slab_measure a b) ≤ ENNReal.ofReal ((24+CV*M^2)*Z.toReal^2)) ∧
      (MemLp (fun z => v12_WDensity (q z)) 2 (v12_slab_measure a b) ∧
        eLpNorm (fun z => v12_WDensity (q z)) 2 (v12_slab_measure a b) ≤ 2*Z^2) := by
  obtain ⟨CA, hCA, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  obtain ⟨CV, hCV, hVb⟩ := v12_actualPotential_L2_budget hHLS
  refine ⟨CA, hCA, CV, hCV, ?_⟩
  intro a b q hc hq M hM hE Z hZ hb
  let V := v12_originalReconstructedPotential a b q hq
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
    simp only [v12_actualCoulombA, ext, hz]
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
  have hv := v12_originalReconstructedPotential_extension_ae hHLS a b q hc hq M hE
  have hv4 := v12_original_V_memLp_of_representative (v12_slab_measure a b) V _ hv
  have hvb := v12_original_V_budget_of_representative (v12_slab_measure a b) V _ hv
    ((24+CV*M^2)*Z.toReal^2) (hVb a b ext hm h4 M hM hEe Z hZ hbe)
  have hnonneg : 0 ≤ (24+CV*M^2)*Z.toReal^2 :=
    mul_nonneg (add_nonneg (by norm_num) (mul_nonneg hCV (sq_nonneg M))) (sq_nonneg _)
  have hW := v12_actual_W_mass_L2_budgets (v12_slab_measure a b) q hq
  refine ⟨hAs, ⟨hv4, (ENNReal.le_ofReal_iff_toReal_le hv4.eLpNorm_ne_top hnonneg).mpr hvb⟩,
    hW.1, ?_⟩
  exact hW.2.2.1.trans (mul_le_mul' le_rfl (pow_le_pow_left' hb 2))

#print axioms v12_original_reconstructed_coefficient_budgets
end SMScattering.W20Full
