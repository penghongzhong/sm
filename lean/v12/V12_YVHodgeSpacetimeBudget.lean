import lean.v12.V12_YUHodgeEnergyL4Application
import lean.v12.V12_YSpacetimeSlices

/-! Derive the actual spacetime Hodge MZ budget by Tonelli from the spatial
HLS application. The raw coefficient is the original integral at every point. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_eLpNorm_four_power
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 4 μ ^ 4 = ∫⁻ z, ‖f z‖ₑ ^ (4 : ℕ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (4 : NNReal)) (by norm_num) hf
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] using h

theorem v12_spatial_L4_budget_to_spacetime
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure ℝ) [SFinite μ]
    (A : V12Spacetime → E) (q : V12Spacetime → F)
    (hA : AEStronglyMeasurable A (μ.prod (volume : Measure V12Spatial)))
    (hq : AEStronglyMeasurable q (μ.prod (volume : Measure V12Spatial)))
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hb : ∀ᵐ t ∂μ, eLpNorm (fun x => A (t,x)) 4 volume ≤
      K * eLpNorm (fun x => q (t,x)) 4 volume) :
    eLpNorm A 4 (μ.prod (volume : Measure V12Spatial)) ≤
      K * eLpNorm q 4 (μ.prod (volume : Measure V12Spatial)) := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [mul_pow, v12_eLpNorm_four_power _ A hA, v12_eLpNorm_four_power _ q hq]
  rw [lintegral_prod _ (hA.enorm.pow_const 4), lintegral_prod _ (hq.enorm.pow_const 4)]
  rw [← lintegral_const_mul' (K^4) _ (by finiteness)]
  apply lintegral_mono_ae
  filter_upwards [hb, hA.prodMk_left, hq.prodMk_left] with t ht hAt hqt
  rw [← v12_eLpNorm_four_power _ _ hAt, ← v12_eLpNorm_four_power _ _ hqt, ← mul_pow]
  exact pow_le_pow_left' ht 4

noncomputable def v12_spacetimeHodge (q : V12Spacetime → V12Field) (z : V12Spacetime) : V12Spatial :=
  v12_rawHodgePotential (fun y => v12_curvatureDensity (q (z.1,y))) z.2

theorem v12_spacetimeHodge_stronglyMeasurable
    (q : V12Spacetime → V12Field) (hq : StronglyMeasurable q) :
    StronglyMeasurable (v12_spacetimeHodge q) := by
  have hB : StronglyMeasurable (fun p : V12Spacetime × V12Spatial =>
      v12_curvatureDensity (q (p.1.1,p.2))) :=
    v12_curvatureDensity_continuous.stronglyMeasurable.comp_measurable
      (hq.measurable.comp (measurable_fst.fst.prodMk measurable_snd))
  have hK : StronglyMeasurable (fun p : V12Spacetime × V12Spatial =>
      v12_hodgeKernel (p.1.2-p.2)) :=
    (v12_hodgeKernel_measurable.comp (measurable_fst.snd.sub measurable_snd)).stronglyMeasurable
  exact (hB.smul hK).integral_prod_right'

theorem v12_actual_hodge_spacetime_MZ (hHLS : V12ExternalHLS2D) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (a b : ℝ) (q : V12Spacetime → V12Field),
      StronglyMeasurable q → MemLp q 4 (v12_slab_measure a b) →
      ∀ M : ℝ≥0∞, M ≠ ∞ →
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ M) →
      MemLp (v12_spacetimeHodge q) 4 (v12_slab_measure a b) ∧
      eLpNorm (v12_spacetimeHodge q) 4 (v12_slab_measure a b) ≤
        C * M * eLpNorm q 4 (v12_slab_measure a b) := by
  obtain ⟨c, hc, hH⟩ := v12_actual_hodge_energy_L4_bound hHLS
  let C := ENNReal.ofReal ((2 * Real.pi)⁻¹ * c) * 2
  refine ⟨C, by dsimp [C]; finiteness, ?_⟩
  intro a b q hq h4 M hM hE
  let μ := (volume : Measure ℝ).restrict (Set.Icc a b)
  have hA := (v12_spacetimeHodge_stronglyMeasurable q hq).aestronglyMeasurable
    (μ := μ.prod (volume : Measure V12Spatial))
  have hb : ∀ᵐ t ∂μ, eLpNorm (fun x => v12_spacetimeHodge q (t,x)) 4 volume ≤
      (C * M) * eLpNorm (fun x => q (t,x)) 4 volume := by
    filter_upwards [hE, v12_spacetime_memLp_slices μ 4 (by norm_num) (by norm_num) q h4] with t ht hqt
    have h2 : MemLp (fun x => q (t,x)) 2 (volume : Measure V12Spatial) := ht.trans_lt hM.lt_top
    have hh := (hH (fun x => q (t,x)) h2 hqt).2
    apply hh.trans
    dsimp [C]
    calc
      _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * c) *
          (2 * (M * eLpNorm (fun x => q (t,x)) 4 volume)) := by gcongr
      _ = _ := by ac_rfl
  have hn := v12_spatial_L4_budget_to_spacetime μ (v12_spacetimeHodge q) q hA
    hq.aestronglyMeasurable (C * M) (by dsimp [C]; finiteness) hb
  refine ⟨?_, hn⟩
  apply hn.trans_lt
  finiteness [h4.eLpNorm_ne_top]

#print axioms v12_eLpNorm_four_power
#print axioms v12_spatial_L4_budget_to_spacetime
#print axioms v12_spacetimeHodge_stronglyMeasurable
#print axioms v12_actual_hodge_spacetime_MZ
end SMScattering.W20Full
