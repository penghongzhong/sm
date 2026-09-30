import lean.v12.V12_YSFActualTemporalCoulomb
import lean.v12.V12_YSZFourierReality

/-! The actual joint Riesz realization and reconstructed A0 retain real
values, including the product-measure measurability needed to reassemble
almost-everywhere time slices. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

def v12_LpIsReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Lp ℂ 2 μ) : Prop :=
  ∀ᵐ z ∂μ, star (f z) = f z

theorem v12_spacetimeCoulombRieszOperator_real (μ : Measure ℝ) [SFinite μ]
    (j k : Fin 2) (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)))
    (hf : v12_LpIsReal (μ.prod volume) f) :
    v12_LpIsReal (μ.prod volume) (v12_spacetimeCoulombRieszOperator μ j k f) := by
  let G := v12_spacetimeCoulombRieszOperator μ j k f
  let hm := Lp.aestronglyMeasurable G
  let g := hm.mk (G : V12Spacetime → ℂ)
  have hgm : StronglyMeasurable g := hm.stronglyMeasurable_mk
  have hg : (G : V12Spacetime → ℂ) =ᵐ[μ.prod volume] g := hm.ae_eq_mk
  have hs : ∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure V12Spatial), star (g (t,x)) = g (t,x) := by
    filter_upwards [v12_fubiniMap_sections μ f, Measure.ae_ae_of_ae_prod hf,
      v12_spacetimeCoulombRieszOperator_sections μ j k f, Measure.ae_ae_of_ae_prod hg]
      with t hi hreal ho hgt
    have hr : ∀ᵐ x ∂(volume : Measure V12Spatial),
        star (v12_fubiniMap μ f t x) = v12_fubiniMap μ f t x := by
      filter_upwards [hi, hreal] with x hix hrx
      rw [hix]
      exact hrx
    have hR := v12_coulombRieszOperator_real j k (v12_fubiniMap μ f t) hr
    filter_upwards [ho, hR, hgt] with x hox hrx hgx
    change G (t,x) = v12_coulombRieszOperator j k (v12_fubiniMap μ f t) x at hox
    rw [← hgx, hox]
    exact hrx
  have hglobal : ∀ᵐ z ∂μ.prod (volume : Measure V12Spatial), star (g z) = g z :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq hgm.measurable.star hgm.measurable)).2 hs
  filter_upwards [hg, hglobal] with z hz hr
  rw [hz]
  exact hr

theorem v12_LpIsReal_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Lp ℂ 2 μ) (hf : v12_LpIsReal μ f) (hg : v12_LpIsReal μ g) :
    v12_LpIsReal μ (f-g) := by
  filter_upwards [Lp.coeFn_sub f g, hf, hg] with z hz hfz hgz
  simp only [hz, Pi.sub_apply, star_sub, hfz, hgz]

theorem v12_LpIsReal_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Lp ℂ 2 μ) (hf : v12_LpIsReal μ f) (hg : v12_LpIsReal μ g) :
    v12_LpIsReal μ (f+g) := by
  filter_upwards [Lp.coeFn_add f g, hf, hg] with z hz hfz hgz
  simp only [hz, Pi.add_apply, star_add, hfz, hgz]

theorem v12_LpIsReal_smul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c : ℂ) (hc : star c = c) (f : Lp ℂ 2 μ) (hf : v12_LpIsReal μ f) :
    v12_LpIsReal μ (c • f) := by
  filter_upwards [Lp.coeFn_smul c f, hf] with z hz hfz
  simp only [hz, Pi.smul_apply, smul_eq_mul, Complex.star_def, map_mul] at *
  rw [hc, hfz]

theorem v12_LpIsReal_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (f : ι → Lp ℂ 2 μ) (hf : ∀ i ∈ s, v12_LpIsReal μ (f i)) :
    v12_LpIsReal μ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with z hz
      simp [hz]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact v12_LpIsReal_add μ _ _ (hf i (Finset.mem_insert_self _ _))
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

theorem v12_actualTemporalCoulomb_real (a b : ℝ)
    (q : V12Spacetime → V12Field) (hq : MemLp q 4 (v12_slab_measure a b)) :
    v12_LpIsReal (v12_slab_measure a b) (v12_actualTemporalCoulombL2 a b q hq) := by
  let μ := v12_slab_measure a b
  have hS (j k : Fin 2) : v12_LpIsReal μ (v12_SL2Class μ j k q hq) := by
    filter_upwards [v12_SL2Class_ae μ j k q hq] with z hz
    simp only [hz, Complex.star_def, Complex.conj_ofReal]
  have hT (j k : Fin 2) := v12_spacetimeCoulombRieszOperator_real
    ((volume : Measure ℝ).restrict (Set.Icc a b)) j k (v12_SL2Class μ j k q hq) (hS j k)
  have hm : v12_LpIsReal μ (v12_massComplexL2Class μ q hq) := by
    filter_upwards [v12_massComplexL2Class_ae μ q hq] with z hz
    simp only [hz, Complex.star_def, Complex.conj_ofReal]
  exact v12_LpIsReal_sub μ _ _
    (v12_LpIsReal_smul μ 4 (by simp) _
      (v12_LpIsReal_sum μ Finset.univ _ (fun j _ =>
        v12_LpIsReal_sum μ Finset.univ _ (fun k _ => hT j k))))
    (v12_LpIsReal_smul μ 2 (by simp) _ hm)

#print axioms v12_spacetimeCoulombRieszOperator_real
#print axioms v12_actualTemporalCoulomb_real
end SMScattering.W20Full
