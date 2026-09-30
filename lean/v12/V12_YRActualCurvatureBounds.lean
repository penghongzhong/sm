import lean.v12.V12_YQuadraticLocalLimits

/-!
The actual B=4 Im(conj(Q0)Q1) density obeys the sharp coefficient2 energy and
spacetime quadratic bounds. These are bounds on the raw continuum field,
not scalar budget variables. Hodge/HLS application remains separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_curvatureDensity_continuous : Continuous v12_curvatureDensity := by
  have h0 : Continuous (fun q : V12Field => q 0) := (EuclideanSpace.proj (𝕜 := ℂ) 0).continuous
  have h1 : Continuous (fun q : V12Field => q 1) := (EuclideanSpace.proj (𝕜 := ℂ) 1).continuous
  unfold v12_curvatureDensity
  fun_prop

theorem v12_curvatureDensity_eLpNorm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : Ω → V12Field) (p : ℝ≥0∞) (hq : AEStronglyMeasurable q μ) :
    eLpNorm (fun z => v12_curvatureDensity (q z)) p μ ≤
      2 * (eLpNorm q (p * 2) μ) ^ 2 := by
  have hB := v12_curvatureDensity_continuous.comp_aestronglyMeasurable hq
  have hmono := eLpNorm_mono_ae_real (p := p) hB
    (Filter.Eventually.of_forall (fun z => v12_curvatureDensity_bound (q z)))
  have hpow : eLpNorm (fun z => ‖q z‖ ^ 2) p μ = (eLpNorm q (p * 2) μ) ^ 2 := by
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_natCast] using
      (eLpNorm_norm_rpow (p := p) (q := (2 : ℝ)) q hq (by norm_num))
  have h2 : ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) := by
    rw [← ofReal_norm]
    norm_num
  apply hmono.trans
  change eLpNorm ((2 : ℝ) • (fun z => ‖q z‖ ^ 2)) p μ ≤ _
  rw [eLpNorm_const_smul, h2, hpow]

theorem v12_curvatureDensity_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : Ω → V12Field) (p : ℝ≥0∞) (hq : MemLp q (p * 2) μ) :
    MemLp (fun z => v12_curvatureDensity (q z)) p μ := by
  have hfinite := hq.eLpNorm_ne_top
  apply (v12_curvatureDensity_eLpNorm_le μ q p hq.aestronglyMeasurable).trans_lt
  finiteness

theorem v12_curvatureDensity_energy_bound
    (q : V12Spatial → V12Field) (hq : MemLp q 2 (volume : Measure V12Spatial))
    (M : ℝ≥0∞) (hM : eLpNorm q 2 (volume : Measure V12Spatial) ≤ M) :
    eLpNorm (fun x => v12_curvatureDensity (q x)) 1 (volume : Measure V12Spatial) ≤ 2 * M ^ 2 := by
  have h := v12_curvatureDensity_eLpNorm_le (volume : Measure V12Spatial) q 1 hq.aestronglyMeasurable
  simp only [one_mul] at h
  apply h.trans
  gcongr

theorem v12_curvatureDensity_spacetime_bound
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b))
    (Z : ℝ≥0∞) (hZ : eLpNorm q 4 (v12_slab_measure a b) ≤ Z) :
    eLpNorm (fun z => v12_curvatureDensity (q z)) 2 (v12_slab_measure a b) ≤ 2 * Z ^ 2 := by
  have h := v12_curvatureDensity_eLpNorm_le (v12_slab_measure a b) q 2 hq.aestronglyMeasurable
  norm_num only at h
  apply h.trans
  gcongr

#print axioms v12_curvatureDensity_eLpNorm_le
#print axioms v12_curvatureDensity_memLp
#print axioms v12_curvatureDensity_energy_bound
#print axioms v12_curvatureDensity_spacetime_bound
end SMScattering.W20Full
