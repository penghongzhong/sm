import lean.v12.V12_YZZCAOriginalReconstructedBudgets

/-! Single-field coefficient budgets on a closed-continuous field: the spatial
L1 curvature bound, spacetime L2 curvature bound, vector Hodge L4 bound,
actual A0 L2 class, raw W and raw V. Constants are uniform in the interval
and field. Every coefficient budget is derived, never an input. Pending CI.
This does not certify the full manuscript coefficient lemma: that also
includes two-field difference bounds and the rough measurable setting. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_single_field_coefficient_budgets (hHLS : V12ExternalHLS2D) :
    ∃ CA : ℝ≥0∞, CA ≠ ∞ ∧ ∃ CV : ℝ, 0 ≤ CV ∧
    ∀ (a b : ℝ) (q : V12Spacetime → V12Field)
      (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
      (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ), 0 ≤ M →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) →
      ∀ (Z : ℝ≥0∞), Z ≠ ∞ → eLpNorm q 4 (v12_slab_measure a b) ≤ Z →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => v12_curvatureDensity (q (t,x))) 1 volume ≤
          2 * (ENNReal.ofReal M)^2) ∧
      (MemLp (fun z => v12_curvatureDensity (q z)) 2 (v12_slab_measure a b) ∧
        eLpNorm (fun z => v12_curvatureDensity (q z)) 2 (v12_slab_measure a b) ≤ 2*Z^2) ∧
      (MemLp (v12_spacetimeHodge q) 4 (v12_slab_measure a b) ∧
        eLpNorm (v12_spacetimeHodge q) 4 (v12_slab_measure a b) ≤ CA*ENNReal.ofReal M*Z) ∧
      ‖v12_actualTemporalCoulombL2 a b q hq‖ ≤ 20*Z.toReal^2 ∧
      (MemLp (fun z => v12_WDensity (q z)) 2 (v12_slab_measure a b) ∧
        eLpNorm (fun z => v12_WDensity (q z)) 2 (v12_slab_measure a b) ≤ 2*Z^2) ∧
      (MemLp (v12_originalReconstructedPotential a b q hq) 2 (v12_slab_measure a b) ∧
        eLpNorm (v12_originalReconstructedPotential a b q hq) 2 (v12_slab_measure a b) ≤
          ENNReal.ofReal ((24+CV*M^2)*Z.toReal^2)) := by
  obtain ⟨CA, hCA, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  obtain ⟨_, _, CV, hCV, hBud⟩ := v12_original_reconstructed_coefficient_budgets hHLS
  refine ⟨CA, hCA, CV, hCV, ?_⟩
  intro a b q hc hq M hM hE Z hZ hb
  have hbudd := hBud a b q hc hq M hM hE Z hZ hb
  let ext := v12_smoothSlabExtension a b q
  have h4 := v12_smoothSlabExtension_memLp a b q 4 hq
  have hEe := v12_smoothSlabExtension_energy a b q M hE
  have heH : v12_spacetimeHodge ext =ᵐ[v12_slab_measure a b] v12_spacetimeHodge q :=
    v12_smoothSlabExtension_Hodge_ae a b q
  obtain ⟨hA4, hAb⟩ := hH a b ext
    (v12_smoothSlabExtension_stronglyMeasurable a b q hc) h4
    (ENNReal.ofReal M) (by finiteness) hEe
  have hbe : eLpNorm ext 4 (v12_slab_measure a b) ≤ Z := by
    rw [v12_smoothSlabExtension_eLpNorm]
    exact hb
  refine ⟨?_, ?_, ?_, v12_actualTemporalCoulomb_L2_budget a b q hq Z hZ hb,
    hbudd.2.2, hbudd.2.1⟩
  · filter_upwards [hE] with t ht
    exact v12_curvatureDensity_energy_bound (fun x => q (t,x))
      (ht.trans_lt (by finiteness)) (ENNReal.ofReal M) ht
  · refine ⟨?_, v12_curvatureDensity_spacetime_bound a b q hq Z hb⟩
    apply (v12_curvatureDensity_spacetime_bound a b q hq Z hb).trans_lt
    finiteness
  · refine ⟨hA4.ae_eq heH, ?_⟩
    rw [← eLpNorm_congr_ae heH]
    exact hAb.trans (mul_le_mul' le_rfl hbe)

#print axioms v12_original_single_field_coefficient_budgets
end SMScattering.W20Full
