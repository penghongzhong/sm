import lean.v12.V12_YHodgeInterpolation

/-! Upgrade time-L1 convergence to time-L2 under an actual uniform bound.
The proof acts on measurable functions, not independent scalar budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_bounded_time_L1_to_L2
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → E)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ C)
    (hlim : Tendsto (fun n => ∫ t, ‖f n t‖ ∂μ) atTop (𝓝 0)) :
    (∀ n, MemLp (f n) 2 μ) ∧
      Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal) atTop (𝓝 0) := by
  have h1 : ∀ n, MemLp (f n) 1 μ := fun n => MemLp.of_bound (hf n) C (hb n)
  have h2 : ∀ n, MemLp (f n) 2 μ := fun n => MemLp.of_bound (hf n) C (hb n)
  have htop : ∀ n, eLpNorm (f n) ∞ μ ≤ ENNReal.ofReal C := by
    intro n
    rw [eLpNorm_exponent_top (hf n)]
    exact eLpNormEssSup_le_of_ae_bound (hb n)
  have hsq : ∀ n, (eLpNorm (f n) 2 μ) ^ 2 ≤
      eLpNorm (f n) 1 μ * ENNReal.ofReal C := by
    intro n
    have hh := eLpNorm_smul_le_mul_eLpNorm (p := 1) (q := ∞) (r := 1) (hf n).norm (hf n).norm
    have hp : eLpNorm (fun t => ‖f n t‖ ^ 2) 1 μ = (eLpNorm (f n) 2 μ) ^ 2 := by
      simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, one_mul, ENNReal.rpow_two] using
        (eLpNorm_norm_rpow (p := 1) (q := (2 : ℝ)) (f n) (hf n) (by norm_num))
    change eLpNorm (fun t => ‖f n t‖ * ‖f n t‖) 1 μ ≤
      eLpNorm (fun t => ‖f n t‖) 1 μ * eLpNorm (fun t => ‖f n t‖) ∞ μ at hh
    have hh' : (eLpNorm (f n) 2 μ) ^ 2 ≤ eLpNorm (f n) 1 μ * eLpNorm (f n) ∞ μ := by
      simpa only [← pow_two, hp, eLpNorm_norm (f n) (hf n)] using hh
    exact hh'.trans (mul_le_mul' le_rfl (htop n))
  have heq : ∀ n, (eLpNorm (f n) 1 μ).toReal = ∫ t, ‖f n t‖ ∂μ := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm (hf n), integral_norm_eq_lintegral_enorm (hf n)]
  have hsqR : ∀ n, ((eLpNorm (f n) 2 μ).toReal) ^ 2 ≤ (∫ t, ‖f n t‖ ∂μ) * C := by
    intro n
    have hfin : eLpNorm (f n) 1 μ * ENNReal.ofReal C ≠ ∞ := by finiteness [(h1 n).eLpNorm_ne_top]
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, heq n] using
      ENNReal.toReal_mono hfin (hsq n)
  have hs : Tendsto (fun n => ((eLpNorm (f n) 2 μ).toReal) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) hsqR
    simpa only [zero_mul] using hlim.mul_const C
  refine ⟨h2, ?_⟩
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_zero] using ht


theorem v12_finite_measure_L2_to_fourThirds_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → E)
    (h2 : ∀ n, MemLp (f n) 2 μ)
    (hlim : Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (f n) ((4 : ℝ≥0∞) / 3) μ).toReal) atTop (𝓝 0) := by
  have hp : (4 : ℝ≥0∞) / 3 ≤ 2 := by norm_num
  let K := μ Set.univ ^ ((1 : ℝ) / 4)
  have hK : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have hb : ∀ n, eLpNorm (f n) ((4 : ℝ≥0∞) / 3) μ ≤ eLpNorm (f n) 2 μ * K := by
    intro n
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (h2 n).aestronglyMeasurable
    norm_num [ENNReal.toReal_div] at h
    exact h
  have hbR : ∀ n, (eLpNorm (f n) ((4 : ℝ≥0∞) / 3) μ).toReal ≤
      (eLpNorm (f n) 2 μ).toReal * K.toReal := by
    intro n
    have hn : eLpNorm (f n) 2 μ * K ≠ ∞ := by finiteness [(h2 n).eLpNorm_ne_top]
    simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono hn (hb n)
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) hbR
  simpa only [zero_mul] using hlim.mul_const K.toReal

#print axioms v12_finite_measure_L2_to_fourThirds_limit
#print axioms v12_bounded_time_L1_to_L2
end SMScattering.W20Full
