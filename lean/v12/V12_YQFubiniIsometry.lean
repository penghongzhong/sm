import lean.v12.V12_YPGenericLpSections

/-! Construct the scalar spacetime-to-Bochner L2 isometry from the actual
raw sections. Its inverse/onto property remains a separate standard step. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_scalarSections (f : V12Spacetime → ℂ) (t : ℝ) : V12ScalarL2 :=
  if h : MemLp (fun x => f (t,x)) 2 (volume : Measure V12Spatial)
  then h.toLp (fun x => f (t,x)) else 0

theorem v12_scalarSections_ae (μ : Measure ℝ) [SFinite μ]
    (f : V12Spacetime → ℂ) (hf : MemLp f 2 (μ.prod (volume : Measure V12Spatial))) :
    ∀ᵐ t ∂μ, (v12_scalarSections f t : V12Spatial → ℂ) =ᵐ[volume] fun x => f (t,x) := by
  have hi := hf.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
  filter_upwards [hi.prod_right_ae, hf.aestronglyMeasurable.prodMk_left] with t hit hmt
  have hm := (integrable_norm_rpow_iff hmt (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp hit
  simp only [v12_scalarSections, dif_pos hm]
  exact hm.coeFn_toLp

theorem v12_scalarSections_memLp (μ : Measure ℝ) [SFinite μ]
    (f : V12Spacetime → ℂ) (hf : MemLp f 2 (μ.prod (volume : Measure V12Spatial))) :
    MemLp (v12_scalarSections f) 2 μ := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have he := v12_generic_eLpNorm_sections_eq_spacetime μ 2 f hf.aestronglyMeasurable
    (v12_scalarSections f) (v12_scalarSections_ae μ f hf)
  exact he.trans_lt hf

noncomputable def v12_fubiniMap (μ : Measure ℝ) [SFinite μ]
    (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) : Lp V12ScalarL2 2 μ :=
  (v12_scalarSections_memLp μ f (Lp.memLp f)).toLp (v12_scalarSections f)

theorem v12_fubiniMap_sections (μ : Measure ℝ) [SFinite μ]
    (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
    ∀ᵐ t ∂μ, (v12_fubiniMap μ f t : V12Spatial → ℂ) =ᵐ[volume] fun x => f (t,x) := by
  filter_upwards [(v12_scalarSections_memLp μ f (Lp.memLp f)).coeFn_toLp,
    v12_scalarSections_ae μ f (Lp.memLp f)] with t ht hs
  change v12_fubiniMap μ f t = v12_scalarSections f t at ht
  rw [ht]
  exact hs

theorem v12_fubiniMap_norm (μ : Measure ℝ) [SFinite μ]
    (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) : ‖v12_fubiniMap μ f‖ = ‖f‖ := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  rw [Lp.norm_def, Lp.norm_def,
    v12_generic_eLpNorm_sections_eq_spacetime μ 2 f (Lp.aestronglyMeasurable f)
      (v12_fubiniMap μ f) (v12_fubiniMap_sections μ f)]

theorem v12_fubiniMap_add (μ : Measure ℝ) [SFinite μ]
    (f g : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
    v12_fubiniMap μ (f+g) = v12_fubiniMap μ f + v12_fubiniMap μ g := by
  apply Lp.ext_iff.mpr
  filter_upwards [v12_fubiniMap_sections μ (f+g), v12_fubiniMap_sections μ f,
    v12_fubiniMap_sections μ g, Lp.coeFn_add (v12_fubiniMap μ f) (v12_fubiniMap μ g),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add f g)] with t hfg hf hg ht hadd
  rw [ht, Pi.add_apply]
  apply Lp.ext_iff.mpr
  filter_upwards [hfg, hf, hg, hadd, Lp.coeFn_add (v12_fubiniMap μ f t) (v12_fubiniMap μ g t)]
    with x hfgx hfx hgx haddx hsum
  simp only [hfgx, haddx, hsum, Pi.add_apply, hfx, hgx]

theorem v12_fubiniMap_smul (μ : Measure ℝ) [SFinite μ] (c : ℂ)
    (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
    v12_fubiniMap μ (c • f) = c • v12_fubiniMap μ f := by
  apply Lp.ext_iff.mpr
  filter_upwards [v12_fubiniMap_sections μ (c • f), v12_fubiniMap_sections μ f,
    Lp.coeFn_smul c (v12_fubiniMap μ f), Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c f)]
    with t hcf hf ht hsm
  rw [ht, Pi.smul_apply]
  apply Lp.ext_iff.mpr
  filter_upwards [hcf, hf, hsm, Lp.coeFn_smul c (v12_fubiniMap μ f t)] with x hcfx hfx hsmx hcx
  simp only [hcfx, hsmx, hcx, Pi.smul_apply, hfx]

noncomputable def v12_fubiniL2Isometry (μ : Measure ℝ) [SFinite μ] :
    Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)) →ₗᵢ[ℂ] Lp V12ScalarL2 2 μ where
  toFun := v12_fubiniMap μ
  map_add' := v12_fubiniMap_add μ
  map_smul' := v12_fubiniMap_smul μ
  norm_map' := v12_fubiniMap_norm μ

#print axioms v12_fubiniMap_sections
#print axioms v12_fubiniMap_norm
#print axioms v12_fubiniL2Isometry
end SMScattering.W20Full
