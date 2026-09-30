import lean.v12.V12_YRActualCurvatureBounds

/-! Pointwise and actual spacetime L2 budgets for W and mass, derived
from the original two-component Q field. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_WDensity (q : V12Field) : ℂ := 2 * ((q 0)^2 + (q 1)^2)
noncomputable def v12_massDensity (q : V12Field) : ℝ := ‖q‖ ^ 2

theorem v12_WDensity_continuous : Continuous v12_WDensity := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).continuous
  have h1 := (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).continuous
  exact continuous_const.mul ((h0.pow 2).add (h1.pow 2))

theorem v12_WDensity_bound (q : V12Field) : ‖v12_WDensity q‖ ≤ 2*‖q‖^2 := by
  have he : ‖q‖ ^ 2 = ‖q 0‖ ^ 2 + ‖q 1‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  unfold v12_WDensity
  rw [norm_mul, Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [Complex.norm_pow, he] using norm_add_le ((q 0)^2) ((q 1)^2)

theorem v12_quadratic_map_L2_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (P : V12Field → E) (hP : Continuous P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ q, ‖P q‖ ≤ C*‖q‖^2)
    (q : Ω → V12Field) (hq : AEStronglyMeasurable q μ) :
    eLpNorm (fun z => P (q z)) 2 μ ≤ ENNReal.ofReal C * (eLpNorm q 4 μ)^2 := by
  have hm := eLpNorm_mono_ae_real (p := (2 : ℝ≥0∞)) (hP.comp_aestronglyMeasurable hq)
    (Filter.Eventually.of_forall (fun z => hb (q z)))
  have he : eLpNorm (fun z => ‖q z‖ ^ 2) 2 μ = (eLpNorm q 4 μ)^2 := by
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_two,
      show (2 : ℝ≥0∞)*2 = 4 by norm_num] using
      eLpNorm_norm_rpow (p := (2 : ℝ≥0∞)) (q := (2 : ℝ)) q hq (by norm_num)
  have hc : eLpNorm (fun z => C*‖q z‖^2) 2 μ = ENNReal.ofReal C * (eLpNorm q 4 μ)^2 := by
    change eLpNorm (C • (fun z => ‖q z‖^2)) 2 μ = _
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg hC, he]
  exact hm.trans_eq hc

theorem v12_actual_W_mass_L2_budgets
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : Ω → V12Field) (hq : MemLp q 4 μ) :
    MemLp (fun z => v12_WDensity (q z)) 2 μ ∧
    MemLp (fun z => v12_massDensity (q z)) 2 μ ∧
    eLpNorm (fun z => v12_WDensity (q z)) 2 μ ≤ 2*(eLpNorm q 4 μ)^2 ∧
    eLpNorm (fun z => v12_massDensity (q z)) 2 μ ≤ (eLpNorm q 4 μ)^2 := by
  have hW := v12_quadratic_map_L2_bound μ v12_WDensity v12_WDensity_continuous
    2 (by norm_num) v12_WDensity_bound q hq.aestronglyMeasurable
  have hm := v12_quadratic_map_L2_bound μ v12_massDensity (continuous_norm.pow 2)
    1 (by norm_num) (fun r => by simp [v12_massDensity, Real.norm_of_nonneg (sq_nonneg _)])
    q hq.aestronglyMeasurable
  norm_num only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, one_mul] at hW hm
  refine ⟨hW.trans_lt ?_, hm.trans_lt ?_, hW, hm⟩ <;> finiteness [hq.eLpNorm_ne_top]

#print axioms v12_WDensity_bound
#print axioms v12_actual_W_mass_L2_budgets
end SMScattering.W20Full
