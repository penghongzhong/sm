import lean.v12.V12_YWCoulombDriftBudget

/-! Original smooth fields need only be continuous on the closed time slab.
Zero extension is globally strongly measurable and agrees with the same
raw field and Hodge coefficient on every time of the slab. This discharges
the global-measurability input without strengthening the original theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_smoothSlabExtension (a b : ℝ) (q : V12Spacetime → V12Field) :
    V12Spacetime → V12Field :=
  (Set.Icc a b ×ˢ Set.univ).indicator q

theorem v12_smoothSlabExtension_stronglyMeasurable
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : ContinuousOn q (Set.Icc a b ×ˢ Set.univ)) :
    StronglyMeasurable (v12_smoothSlabExtension a b q) := by
  classical
  have hm := hq.measurable_piecewise (g := fun _ => (0 : V12Field)) continuousOn_const
    (measurableSet_Icc.prod MeasurableSet.univ)
  exact hm.stronglyMeasurable

theorem v12_smoothSlabExtension_apply
    (a b : ℝ) (q : V12Spacetime → V12Field) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (x : V12Spatial) : v12_smoothSlabExtension a b q (t,x) = q (t,x) :=
  Set.indicator_of_mem (show (t,x) ∈ Set.Icc a b ×ˢ Set.univ from ⟨ht, Set.mem_univ _⟩) q

theorem v12_smoothSlabExtension_ae
    (a b : ℝ) (q : V12Spacetime → V12Field) :
    v12_smoothSlabExtension a b q =ᵐ[v12_slab_measure a b] q := by
  rw [v12_slab_measure, Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
  exact Set.indicator_of_mem hz q

theorem v12_smoothSlabExtension_eLpNorm
    (a b : ℝ) (q : V12Spacetime → V12Field) (p : ℝ≥0∞) :
    eLpNorm (v12_smoothSlabExtension a b q) p (v12_slab_measure a b) =
      eLpNorm q p (v12_slab_measure a b) :=
  eLpNorm_congr_ae (v12_smoothSlabExtension_ae a b q)

theorem v12_smoothSlabExtension_memLp
    (a b : ℝ) (q : V12Spacetime → V12Field) (p : ℝ≥0∞)
    (hq : MemLp q p (v12_slab_measure a b)) :
    MemLp (v12_smoothSlabExtension a b q) p (v12_slab_measure a b) := by
  change eLpNorm (v12_smoothSlabExtension a b q) p (v12_slab_measure a b) < ∞
  rw [v12_smoothSlabExtension_eLpNorm]
  exact hq

theorem v12_smoothSlabExtension_Hodge
    (a b : ℝ) (q : V12Spacetime → V12Field) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (x : V12Spatial) :
    v12_spacetimeHodge (v12_smoothSlabExtension a b q) (t,x) = v12_spacetimeHodge q (t,x) := by
  unfold v12_spacetimeHodge
  have hs : (fun y => v12_curvatureDensity (v12_smoothSlabExtension a b q (t,y))) =
      (fun y => v12_curvatureDensity (q (t,y))) := by
    funext y
    rw [v12_smoothSlabExtension_apply a b q t ht y]
  rw [hs]

theorem v12_smoothSlabExtension_A
    (a b : ℝ) (q : V12Spacetime → V12Field) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (x : V12Spatial) (j : Fin 2) :
    v12_actualCoulombA (v12_smoothSlabExtension a b q) j (t,x) = v12_actualCoulombA q j (t,x) := by
  unfold v12_actualCoulombA
  rw [v12_smoothSlabExtension_Hodge a b q t ht x]

theorem v12_smoothSlabExtension_Hodge_ae
    (a b : ℝ) (q : V12Spacetime → V12Field) :
    v12_spacetimeHodge (v12_smoothSlabExtension a b q) =ᵐ[v12_slab_measure a b]
      v12_spacetimeHodge q := by
  rw [v12_slab_measure, Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
  exact v12_smoothSlabExtension_Hodge a b q z.1 hz.1 z.2

theorem v12_original_slab_Hodge_MZ (hHLS : V12ExternalHLS2D) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (a b : ℝ) (q : V12Spacetime → V12Field),
      ContinuousOn q (Set.Icc a b ×ˢ Set.univ) →
      MemLp q 4 (v12_slab_measure a b) → ∀ M : ℝ≥0∞, M ≠ ∞ →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ M) →
      MemLp (v12_spacetimeHodge q) 4 (v12_slab_measure a b) ∧
      eLpNorm (v12_spacetimeHodge q) 4 (v12_slab_measure a b) ≤
        C * M * eLpNorm q 4 (v12_slab_measure a b) := by
  obtain ⟨C, hC, hMZ⟩ := v12_actual_hodge_spacetime_MZ hHLS
  refine ⟨C, hC, ?_⟩
  intro a b q hcont hq M hM hE
  let ext := v12_smoothSlabExtension a b q
  have hext := v12_smoothSlabExtension_stronglyMeasurable a b q hcont
  have hext4 := v12_smoothSlabExtension_memLp a b q 4 hq
  have hEext : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => ext (t,x)) 2 volume ≤ M := by
    filter_upwards [hE, ae_restrict_mem measurableSet_Icc] with t ht htI
    have he : (fun x => ext (t,x)) = (fun x => q (t,x)) :=
      funext (fun x => v12_smoothSlabExtension_apply a b q t htI x)
    rw [he]
    exact ht
  obtain ⟨hm, hb⟩ := hMZ a b ext hext hext4 M hM hEext
  have hnorm := eLpNorm_congr_ae (v12_smoothSlabExtension_Hodge_ae a b q) (p := (4 : ℝ≥0∞))
  refine ⟨?_, ?_⟩
  · change eLpNorm (v12_spacetimeHodge q) 4 (v12_slab_measure a b) < ∞
    rw [← hnorm]
    exact hm
  · change eLpNorm (v12_spacetimeHodge ext) 4 (v12_slab_measure a b) ≤ _ at hb
    rw [hnorm, v12_smoothSlabExtension_eLpNorm] at hb
    exact hb

#print axioms v12_smoothSlabExtension_stronglyMeasurable
#print axioms v12_smoothSlabExtension_ae
#print axioms v12_smoothSlabExtension_Hodge
#print axioms v12_smoothSlabExtension_A
#print axioms v12_original_slab_Hodge_MZ
end SMScattering.W20Full
