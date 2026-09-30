import lean.v12.V12_YRActualCurvatureBounds

/-! Actual mixed energy/L4 curvature estimate for the HLS application. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_curvatureDensity_mixed_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (q : Ω → V12Field)
    (hq : AEStronglyMeasurable q μ) :
    eLpNorm (fun z => v12_curvatureDensity (q z)) ((4 : ℝ≥0∞) / 3) μ ≤
      2 * (eLpNorm q 2 μ * eLpNorm q 4 μ) := by
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) 4 ((4 : ℝ≥0∞) / 3) :=
    v12_holderTriple_two_four_fourThirds
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 4)
    (r := (4 : ℝ≥0∞) / 3) hq.norm hq.norm
  change eLpNorm (fun z => ‖q z‖ * ‖q z‖) ((4 : ℝ≥0∞) / 3) μ ≤
    eLpNorm (fun z => ‖q z‖) 2 μ * eLpNorm (fun z => ‖q z‖) 4 μ at hh
  simp only [← pow_two, eLpNorm_norm q hq] at hh
  have hm := eLpNorm_mono_ae_real (p := (4 : ℝ≥0∞) / 3)
    (v12_curvatureDensity_continuous.comp_aestronglyMeasurable hq)
    (Filter.Eventually.of_forall (fun z => v12_curvatureDensity_bound (q z)))
  have he : eLpNorm (fun z => (2 : ℝ) * ‖q z‖ ^ 2) ((4 : ℝ≥0∞) / 3) μ =
      2 * eLpNorm (fun z => ‖q z‖ ^ 2) ((4 : ℝ≥0∞) / 3) μ := by
    change eLpNorm ((2 : ℝ) • (fun z => ‖q z‖ ^ 2)) _ μ = _
    rw [eLpNorm_const_smul, ← ofReal_norm]
    norm_num
  rw [he] at hm
  exact hm.trans (mul_le_mul' le_rfl hh)

theorem v12_curvatureDensity_mixed_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (q : Ω → V12Field)
    (h2 : MemLp q 2 μ) (h4 : MemLp q 4 μ) :
    MemLp (fun z => v12_curvatureDensity (q z)) ((4 : ℝ≥0∞) / 3) μ := by
  change eLpNorm _ _ μ < ∞
  apply (v12_curvatureDensity_mixed_bound μ q h2.aestronglyMeasurable).trans_lt
  finiteness [h2.eLpNorm_ne_top, h4.eLpNorm_ne_top]

#print axioms v12_curvatureDensity_mixed_bound
#print axioms v12_curvatureDensity_mixed_memLp
end SMScattering.W20Full
