import lean.v12.V12_YTBochnerSectionNorm

/-!
The original jointly continuous raw field itself defines the slab L2 class.
Its time L2 norm is identified through exact spatial representatives; no
independent slab field or representative equality is supplied as an interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open MeasureTheory
open scoped ENNReal

theorem v12_raw_field_slab_memLp
    (a b : ℝ) (q : ℝ → V12Spatial → V12Field)
    (hq : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hrep : ∀ t ∈ Set.Icc a b, (Q t : V12Spatial → V12Field) =ᵐ[volume] q t) :
    MemLp (Function.uncurry q) 2 (v12_slab_measure a b) ∧
      eLpNorm (Function.uncurry q) 2 (v12_slab_measure a b) =
        eLpNorm Q 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc a b)
  have hraw : AEStronglyMeasurable (Function.uncurry q) (v12_slab_measure a b) := by
    rw [v12_slab_measure, Measure.restrict_prod_eq_prod_univ]
    exact hq.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
  have hQ2 : MemLp Q 2 μ := hQ.mono_exponent le_top
  have hrepAE : ∀ᵐ t ∂μ, (Q t : V12Spatial → V12Field)
      =ᵐ[volume] fun y => Function.uncurry q (t,y) :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => hrep t ht)
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hn := v12_eLpNorm_sections_eq_spacetime μ 2 (Function.uncurry q) hraw Q hrepAE
  exact ⟨hn.symm.trans_lt hQ2, hn.symm⟩

noncomputable def v12_rawSlabClass
    (a b : ℝ) (q : ℝ → V12Spatial → V12Field)
    (hq : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hrep : ∀ t ∈ Set.Icc a b, (Q t : V12Spatial → V12Field) =ᵐ[volume] q t) :
    V12SlabL2 a b :=
  (v12_raw_field_slab_memLp a b q hq Q hQ hrep).1.toLp (Function.uncurry q)

theorem v12_rawSlabClass_ae
    (a b : ℝ) (q : ℝ → V12Spatial → V12Field)
    (hq : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hrep : ∀ t ∈ Set.Icc a b, (Q t : V12Spatial → V12Field) =ᵐ[volume] q t) :
    (v12_rawSlabClass a b q hq Q hQ hrep : V12Spacetime → V12Field)
      =ᵐ[v12_slab_measure a b] Function.uncurry q :=
  (v12_raw_field_slab_memLp a b q hq Q hQ hrep).1.coeFn_toLp

theorem v12_rawSlabClass_norm_eq
    (a b : ℝ) (q : ℝ → V12Spatial → V12Field)
    (hq : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hrep : ∀ t ∈ Set.Icc a b, (Q t : V12Spatial → V12Field) =ᵐ[volume] q t) :
    ‖v12_rawSlabClass a b q hq Q hQ hrep‖ =
      (eLpNorm Q 2 ((volume : Measure ℝ).restrict (Set.Icc a b))).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (v12_rawSlabClass_ae a b q hq Q hQ hrep),
    (v12_raw_field_slab_memLp a b q hq Q hQ hrep).2]

/-- The same time-L2 norm has a finite uniform bound from every-time energy. -/
theorem v12_timeL2_uniform_bound
    (a b M : ℝ) (Q : ℕ → ℝ → V12SpatialL2)
    (hQ : ∀ n, MemLp (Q n) ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hEnergy : ∀ n t, t ∈ Set.Icc a b → ‖Q n t‖ ≤ M) :
    ∃ B : ℝ, ∀ n,
      (eLpNorm (Q n) 2 ((volume : Measure ℝ).restrict (Set.Icc a b))).toReal ≤ B := by
  let μ : Measure ℝ := volume.restrict (Set.Icc a b)
  let E : ℝ≥0∞ := μ Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal M
  have hμ : μ Set.univ ≠ ∞ := (measure_lt_top μ Set.univ).ne
  have hE : E ≠ ∞ := by
    dsimp only [E]
    finiteness
  refine ⟨E.toReal, ?_⟩
  intro n
  apply ENNReal.toReal_mono hE
  exact eLpNorm_le_of_ae_bound (hQ n).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => hEnergy n t ht))

#print axioms v12_rawSlabClass_norm_eq
#print axioms v12_timeL2_uniform_bound

#print axioms v12_raw_field_slab_memLp
#print axioms v12_rawSlabClass_ae

end SMScattering.W20Full
