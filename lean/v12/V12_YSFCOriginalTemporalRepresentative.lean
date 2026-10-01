import lean.v12.V12_YSFBOriginalTemporalSlices
import Mathlib.MeasureTheory.Integral.Prod

/-! The original spatial A0 formula identifies the joint L2 class. The
measurability required for the converse Fubini implication is proved from
closed-slab continuity and strongly measurable representatives. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_slab_continuous_aestronglyMeasurable
    {E : Type} [NormedAddCommGroup E]
    (a b : ℝ) (f : V12Spacetime → E)
    (hf : ContinuousOn f (Set.Icc a b ×ˢ Set.univ)) :
    AEStronglyMeasurable f (v12_slab_measure a b) := by
  rw [v12_slab_measure, Measure.restrict_prod_eq_prod_univ]
  exact hf.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)

theorem v12_ae_eq_of_measurable_sections
    (μ : Measure ℝ) [SFinite μ] (f g : V12Spacetime → ℂ)
    (hf : AEStronglyMeasurable f (μ.prod (volume : Measure V12Spatial)))
    (hg : AEStronglyMeasurable g (μ.prod (volume : Measure V12Spatial)))
    (he : ∀ᵐ t ∂μ, (fun x => f (t,x)) =ᵐ[volume] (fun x => g (t,x))) :
    f =ᵐ[μ.prod (volume : Measure V12Spatial)] g := by
  have hfm := hf.stronglyMeasurable_mk
  have hgm := hg.stronglyMeasurable_mk
  have hs : ∀ᵐ t ∂μ, (fun x => hf.mk f (t,x)) =ᵐ[volume]
      (fun x => hg.mk g (t,x)) := by
    filter_upwards [he, Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with t ht hft hgt
    filter_upwards [hft, ht, hgt] with x hx hy hz
    exact hx.symm.trans (hy.trans hz)
  have hj : hf.mk f =ᵐ[μ.prod (volume : Measure V12Spatial)] hg.mk g :=
    (Measure.ae_prod_iff_ae_ae (hfm.measurableSet_eq_fun hgm)).mpr hs
  exact hf.ae_eq_mk.trans (hj.trans hg.ae_eq_mk.symm)

theorem v12_original_A0_joint_representative
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (A0 : V12Spacetime → ℂ)
    (hc : ContinuousOn A0 (Set.Icc a b ×ˢ Set.univ))
    (hformula : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      ∀ ht : MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial),
      (fun x => A0 (t,x)) =ᵐ[volume]
      (v12_temporalCoulombClass
        (fun j k => v12_SL2Class volume j k (fun x => q (t,x)) ht)
        (v12_massComplexL2Class volume (fun x => q (t,x)) ht) : V12Spatial → ℂ)) :
    A0 =ᵐ[v12_slab_measure a b] v12_actualTemporalCoulombL2 a b q hq := by
  let μ := (volume : Measure ℝ).restrict (Set.Icc a b)
  have hslices : ∀ᵐ t ∂μ, MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial) := by
    have hi := hq.integrable_norm_rpow (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞)
    filter_upwards [hi.prod_right_ae, hq.aestronglyMeasurable.prodMk_left] with t ht hm
    exact (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).mp ht
  apply v12_ae_eq_of_measurable_sections μ A0 _
    (v12_slab_continuous_aestronglyMeasurable a b A0 hc)
    (Lp.aestronglyMeasurable _)
  filter_upwards [hformula, v12_A0_original_spatial_formula a b q hq,
    hslices]
    with t hf ha ht
  exact (hf ht).trans (ha ht).symm

theorem v12_original_A0_memLp
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (A0 : V12Spacetime → ℂ)
    (he : A0 =ᵐ[v12_slab_measure a b] v12_actualTemporalCoulombL2 a b q hq) :
    MemLp A0 2 (v12_slab_measure a b) :=
  (Lp.memLp (v12_actualTemporalCoulombL2 a b q hq)).ae_eq he.symm

theorem v12_original_A0_L2_budget
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (A0 : V12Spacetime → ℂ)
    (he : A0 =ᵐ[v12_slab_measure a b] v12_actualTemporalCoulombL2 a b q hq)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : eLpNorm q 4 (v12_slab_measure a b) ≤ Z) :
    (eLpNorm A0 2 (v12_slab_measure a b)).toReal ≤ 20 * Z.toReal^2 := by
  have hmem := v12_original_A0_memLp a b q hq A0 he
  have hclass : hmem.toLp A0 = v12_actualTemporalCoulombL2 a b q hq :=
    Lp.ext_iff.mpr (hmem.coeFn_toLp.trans he)
  rw [← Lp.norm_toLp A0 hmem, hclass]
  exact v12_actualTemporalCoulomb_L2_budget a b q hq Z hZ hb

#print axioms v12_ae_eq_of_measurable_sections
#print axioms v12_original_A0_joint_representative
#print axioms v12_original_A0_L2_budget
end SMScattering.W20Full
