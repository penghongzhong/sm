import lean.v12.V12_YVHodgeSpacetimeBudget

/-! The actual complex spatial Coulomb components and A_j Q source budget,
with the Hodge MZ estimate derived from the original field. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_actualCoulombA (q : V12Spacetime → V12Field) (j : Fin 2)
    (z : V12Spacetime) : ℂ := ((v12_spacetimeHodge q z) j : ℂ)

theorem v12_actualCoulombA_eLpNorm_le
    (μ : Measure V12Spacetime) (q : V12Spacetime → V12Field)
    (hq : StronglyMeasurable q) (p : ℝ≥0∞) (j : Fin 2) :
    eLpNorm (v12_actualCoulombA q j) p μ ≤ eLpNorm (v12_spacetimeHodge q) p μ := by
  have hA := v12_spacetimeHodge_stronglyMeasurable q hq
  have hc : Continuous (fun x : V12Spatial => (x j : ℂ)) :=
    Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  have hm := eLpNorm_mono_ae_real (μ := μ) (p := p) (f := v12_actualCoulombA q j) (g := fun z => ‖v12_spacetimeHodge q z‖) (hc.comp_stronglyMeasurable hA).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by
      simpa only [Complex.norm_real] using PiLp.norm_apply_le (v12_spacetimeHodge q z) j))
  exact hm.trans_eq (eLpNorm_norm _ hA.aestronglyMeasurable)

theorem v12_actualCoulomb_drift_MZZ (hHLS : V12ExternalHLS2D) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (a b : ℝ) (q : V12Spacetime → V12Field),
      StronglyMeasurable q → MemLp q 4 (v12_slab_measure a b) →
      ∀ M : ℝ≥0∞, M ≠ ∞ →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ M) →
      ∀ j : Fin 2,
        MemLp (v12_driftProduct (v12_actualCoulombA q) q j) 2 (v12_slab_measure a b) ∧
        eLpNorm (v12_driftProduct (v12_actualCoulombA q) q j) 2 (v12_slab_measure a b) ≤
          C * M * (eLpNorm q 4 (v12_slab_measure a b)) ^ 2 := by
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  refine ⟨C, hC, ?_⟩
  intro a b q hq h4 M hM hE j
  obtain ⟨hA4, hAb⟩ := hH a b q hq h4 M hM hE
  have hAj : ∀ k, MemLp (v12_actualCoulombA q k) 4 (v12_slab_measure a b) := by
    intro k
    exact (v12_actualCoulombA_eLpNorm_le _ q hq 4 k).trans_lt hA4
  refine ⟨v12_driftProduct_memLp _ (v12_actualCoulombA q) q j (hAj j) h4, ?_⟩
  apply (v12_driftProduct_eLpNorm_le _ (v12_actualCoulombA q) q j
    (hAj j).aestronglyMeasurable h4.aestronglyMeasurable).trans
  calc
    _ ≤ (C * M * eLpNorm q 4 (v12_slab_measure a b)) * eLpNorm q 4 (v12_slab_measure a b) :=
      mul_le_mul' ((v12_actualCoulombA_eLpNorm_le _ q hq 4 j).trans hAb) le_rfl
    _ = _ := by rw [pow_two, mul_assoc]

#print axioms v12_actualCoulombA_eLpNorm_le
#print axioms v12_actualCoulomb_drift_MZZ
end SMScattering.W20Full
