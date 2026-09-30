import lean.v12.V12_YSFActualTemporalCoulomb

/-! Exact original-field correspondence: joint tensor, S and mass classes
have the SAME raw Q sections. No independent coefficient realization is
assumed. The temporal Coulomb formula is subsequently lifted linearly. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_tensor_fubini_original_sections
    (μ : Measure ℝ) [SFinite μ] (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (μ.prod (volume : Measure V12Spatial))) (j k : Fin 2) :
    ∀ᵐ t ∂μ, ∀ ht : MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial),
      v12_fubiniMap μ (v12_tensorL2Class (μ.prod volume) j k q hq) t =
        v12_tensorL2Class volume j k (fun x => q (t,x)) ht := by
  filter_upwards [v12_fubiniMap_sections μ (v12_tensorL2Class (μ.prod volume) j k q hq),
    Measure.ae_ae_of_ae_prod (v12_tensorDensity_memLp (μ.prod volume) j k q hq).coeFn_toLp]
    with t hf hraw
  intro ht
  apply Lp.ext_iff.mpr
  filter_upwards [hf, hraw, (v12_tensorDensity_memLp volume j k (fun x => q (t,x)) ht).coeFn_toLp]
    with x hfx hrx hsx
  exact hfx.trans (hrx.trans hsx.symm)

theorem v12_S_fubini_original_sections
    (μ : Measure ℝ) [SFinite μ] (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (μ.prod (volume : Measure V12Spatial))) (j k : Fin 2) :
    ∀ᵐ t ∂μ, ∀ ht : MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial),
      v12_fubiniMap μ (v12_SL2Class (μ.prod volume) j k q hq) t =
        v12_SL2Class volume j k (fun x => q (t,x)) ht := by
  filter_upwards [v12_fubiniMap_sections μ (v12_SL2Class (μ.prod volume) j k q hq),
    Measure.ae_ae_of_ae_prod (v12_SL2Class_ae (μ.prod volume) j k q hq)] with t hf hraw
  intro ht
  apply Lp.ext_iff.mpr
  filter_upwards [hf, hraw, v12_SL2Class_ae volume j k (fun x => q (t,x)) ht]
    with x hfx hrx hsx
  exact hfx.trans (hrx.trans hsx.symm)

theorem v12_mass_fubini_original_sections
    (μ : Measure ℝ) [SFinite μ] (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (μ.prod (volume : Measure V12Spatial))) :
    ∀ᵐ t ∂μ, ∀ ht : MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial),
      v12_fubiniMap μ (v12_massComplexL2Class (μ.prod volume) q hq) t =
        v12_massComplexL2Class volume (fun x => q (t,x)) ht := by
  filter_upwards [v12_fubiniMap_sections μ (v12_massComplexL2Class (μ.prod volume) q hq),
    Measure.ae_ae_of_ae_prod (v12_massComplexL2Class_ae (μ.prod volume) q hq)] with t hf hraw
  intro ht
  apply Lp.ext_iff.mpr
  filter_upwards [hf, hraw, v12_massComplexL2Class_ae volume (fun x => q (t,x)) ht]
    with x hfx hrx hsx
  exact hfx.trans (hrx.trans hsx.symm)

theorem v12_Riesz_S_original_sections
    (μ : Measure ℝ) [SFinite μ] (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (μ.prod (volume : Measure V12Spatial))) (j k : Fin 2) :
    ∀ᵐ t ∂μ, ∀ ht : MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial),
      (fun x => v12_spacetimeCoulombRieszOperator μ j k
        (v12_SL2Class (μ.prod volume) j k q hq) (t,x)) =ᵐ[volume]
      (v12_coulombRieszOperator j k
        (v12_SL2Class volume j k (fun x => q (t,x)) ht) : V12Spatial → ℂ) := by
  filter_upwards [v12_spacetimeCoulombRieszOperator_sections μ j k
    (v12_SL2Class (μ.prod volume) j k q hq),
    v12_S_fubini_original_sections μ q hq j k] with t hr hs
  intro ht
  rw [hs ht] at hr
  exact hr

theorem v12_fubiniMap_Riesz (μ : Measure ℝ) [SFinite μ] (j k : Fin 2)
    (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
    v12_fubiniMap μ (v12_spacetimeCoulombRieszOperator μ j k f) =
      v12_timeCoulombRieszOperator μ j k (v12_fubiniMap μ f) := by
  change v12_fubiniL2Equiv μ ((v12_fubiniL2Equiv μ).symm _) = _
  exact (v12_fubiniL2Equiv μ).apply_symm_apply _

theorem v12_actualTemporalCoulomb_fubini_formula
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) :
    v12_fubiniMap ((volume : Measure ℝ).restrict (Set.Icc a b))
      (v12_actualTemporalCoulombL2 a b q hq) =
    (4 : ℂ) • (∑ j, ∑ k, v12_timeCoulombRieszOperator
      ((volume : Measure ℝ).restrict (Set.Icc a b)) j k
      (v12_fubiniMap ((volume : Measure ℝ).restrict (Set.Icc a b))
        (v12_SL2Class (v12_slab_measure a b) j k q hq))) -
    (2 : ℂ) • v12_fubiniMap ((volume : Measure ℝ).restrict (Set.Icc a b))
      (v12_massComplexL2Class (v12_slab_measure a b) q hq) := by
  let μ := (volume : Measure ℝ).restrict (Set.Icc a b)
  have hsub (f g : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
      v12_fubiniMap μ (f-g) = v12_fubiniMap μ f-v12_fubiniMap μ g :=
    (v12_fubiniL2Isometry μ).map_sub f g
  have hsum (F : Fin 2 → Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
      v12_fubiniMap μ (∑ j, F j) = ∑ j, v12_fubiniMap μ (F j) :=
    map_sum (v12_fubiniL2Isometry μ) F Finset.univ
  rw [v12_actualTemporalCoulombL2_eq]
  rw [hsub, v12_fubiniMap_smul, v12_fubiniMap_smul, hsum]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k hk
  exact v12_fubiniMap_Riesz μ j k _

theorem v12_time_temporal_formula_ae
    (μ : Measure ℝ) (S : Fin 2 → Fin 2 → Lp V12ScalarL2 2 μ)
    (m : Lp V12ScalarL2 2 μ) :
    (((4 : ℂ) • (∑ j, ∑ k, v12_timeCoulombRieszOperator μ j k (S j k)) -
      (2 : ℂ) • m : Lp V12ScalarL2 2 μ) : ℝ → V12ScalarL2) =ᵐ[μ]
      fun t => v12_temporalCoulombClass (fun j k => S j k t) (m t) := by
  let R := fun j k => v12_timeCoulombRieszOperator μ j k (S j k)
  let B := ∑ j, ∑ k, R j k
  have hR : ∀ᵐ t ∂μ, ∀ j k, R j k t = v12_coulombRieszOperator j k (S j k t) :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => v12_timeCoulombRieszOperator_ae μ j k (S j k)))
  have hinner : ∀ᵐ t ∂μ, ∀ j, (∑ k, R j k) t = ∑ k, R j k t :=
    ae_all_iff.mpr (fun j => Lp.coeFn_fun_finsetSum Finset.univ (R j))
  have hB : ∀ᵐ t ∂μ, B t = ∑ j, ∑ k, v12_coulombRieszOperator j k (S j k t) := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => ∑ k, R j k), hinner, hR]
      with t ho hi hr
    change B t = _ at ho
    rw [ho]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hi j]
    apply Finset.sum_congr rfl
    intro k hk
    exact hr j k
  filter_upwards [Lp.coeFn_sub ((4 : ℂ) • B) ((2 : ℂ) • m),
    Lp.coeFn_smul (4 : ℂ) B, Lp.coeFn_smul (2 : ℂ) m, hB] with t hsub h4 h2 hb
  change ((4 : ℂ) • B - (2 : ℂ) • m) t = _
  rw [hsub, Pi.sub_apply, h4, Pi.smul_apply, h2, Pi.smul_apply, hb]
  rfl

theorem v12_A0_original_spatial_formula
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      ∀ ht : MemLp (fun x => q (t,x)) 4 (volume : Measure V12Spatial),
      (fun x => v12_actualTemporalCoulombL2 a b q hq (t,x)) =ᵐ[volume]
      (v12_temporalCoulombClass
        (fun j k => v12_SL2Class volume j k (fun x => q (t,x)) ht)
        (v12_massComplexL2Class volume (fun x => q (t,x)) ht) : V12Spatial → ℂ) := by
  let μ := (volume : Measure ℝ).restrict (Set.Icc a b)
  let S := fun j k => v12_fubiniMap μ (v12_SL2Class (v12_slab_measure a b) j k q hq)
  let m := v12_fubiniMap μ (v12_massComplexL2Class (v12_slab_measure a b) q hq)
  have hA := v12_time_temporal_formula_ae μ S m
  rw [← v12_actualTemporalCoulomb_fubini_formula a b q hq] at hA
  have hS : ∀ᵐ t ∂μ, ∀ j k, ∀ ht : MemLp (fun x => q (t,x)) 4 volume,
      S j k t = v12_SL2Class volume j k (fun x => q (t,x)) ht :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => v12_S_fubini_original_sections μ q hq j k))
  filter_upwards [v12_fubiniMap_sections μ (v12_actualTemporalCoulombL2 a b q hq),
    hA, hS, v12_mass_fubini_original_sections μ q hq] with t hf ha hs hm
  intro ht
  have hclasses : v12_fubiniMap μ (v12_actualTemporalCoulombL2 a b q hq) t =
      v12_temporalCoulombClass
        (fun j k => v12_SL2Class volume j k (fun x => q (t,x)) ht)
        (v12_massComplexL2Class volume (fun x => q (t,x)) ht) := by
    rw [ha]
    have he : (fun j k => S j k t) = (fun j k => v12_SL2Class volume j k (fun x => q (t,x)) ht) :=
      funext (fun j => funext (fun k => hs j k ht))
    rw [he, hm ht]
  rw [hclasses] at hf
  exact hf.symm

#print axioms v12_tensor_fubini_original_sections
#print axioms v12_S_fubini_original_sections
#print axioms v12_mass_fubini_original_sections
#print axioms v12_Riesz_S_original_sections
#print axioms v12_fubiniMap_Riesz
#print axioms v12_actualTemporalCoulomb_fubini_formula
#print axioms v12_A0_original_spatial_formula
end SMScattering.W20Full
