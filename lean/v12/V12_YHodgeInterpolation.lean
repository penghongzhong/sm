import lean.v12.V12_SourceProducts

/-! The concrete L^(4/3)-L4 interpolation inequality needed for local Hodge
L2 convergence. It is derived by Holder applied to norm(f)*norm(f). -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_holderTriple_fourThirds_four_one :
    ENNReal.HolderTriple ((4 : ℝ≥0∞) / 3) 4 1 := by
  have h : Real.HolderTriple ((4 : ℝ) / 3) 4 1 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have he : ENNReal.ofReal ((4 : ℝ) / 3) = (4 : ℝ≥0∞) / 3 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  simpa only [he, ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

theorem v12_hodge_L2_interpolation_squared
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ) ^ 2 ≤ eLpNorm f ((4 : ℝ≥0∞) / 3) μ * eLpNorm f 4 μ := by
  letI : ENNReal.HolderTriple ((4 : ℝ≥0∞) / 3) 4 1 :=
    v12_holderTriple_fourThirds_four_one
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := (4 : ℝ≥0∞) / 3)
    (q := 4) (r := 1) hf.norm hf.norm
  have hp : eLpNorm (fun z => ‖f z‖ ^ 2) 1 μ = (eLpNorm f 2 μ) ^ 2 := by
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, one_mul, ENNReal.rpow_natCast] using
      (eLpNorm_norm_rpow (p := 1) (q := (2 : ℝ)) f hf (by norm_num))
  simpa only [smul_eq_mul, ← pow_two, hp, eLpNorm_norm f hf] using hh


/-- Local L^(4/3) convergence and a uniform L4 bound force actual L2
convergence; no L2 interpolation conclusion is an input. -/
theorem v12_hodge_L2_limit_of_fourThirds_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : ℕ → Ω → E)
    (h43 : ∀ n, MemLp (f n) ((4 : ℝ≥0∞) / 3) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (h4 : ∀ n, eLpNorm (f n) 4 μ ≤ C)
    (hlim : Tendsto (fun n => (eLpNorm (f n) ((4 : ℝ≥0∞) / 3) μ).toReal)
      atTop (𝓝 0)) :
    (∀ n, MemLp (f n) 2 μ) ∧
      Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal) atTop (𝓝 0) := by
  have hb : ∀ n, (eLpNorm (f n) 2 μ) ^ 2 ≤
      eLpNorm (f n) ((4 : ℝ≥0∞) / 3) μ * C := by
    intro n
    exact (v12_hodge_L2_interpolation_squared μ (f n) (h43 n).aestronglyMeasurable).trans
      (mul_le_mul_left' (h4 n) _)
  have hfin : ∀ n, eLpNorm (f n) ((4 : ℝ≥0∞) / 3) μ * C < ∞ := by
    intro n
    exact ENNReal.mul_lt_top (h43 n) hC.lt_top
  have h2 : ∀ n, MemLp (f n) 2 μ := by
    intro n
    have hh := (hb n).trans_lt (hfin n)
    simpa [ENNReal.pow_lt_top_iff] using hh
  refine ⟨h2, ?_⟩
  have hbR : ∀ n, ((eLpNorm (f n) 2 μ).toReal) ^ 2 ≤
      (eLpNorm (f n) ((4 : ℝ≥0∞) / 3) μ).toReal * C.toReal := by
    intro n
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul] using
      ENNReal.toReal_mono (hfin n).ne (hb n)
  have hs : Tendsto (fun n => ((eLpNorm (f n) 2 μ).toReal) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) hbR
    simpa only [zero_mul] using hlim.mul_const C.toReal
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_zero] using ht

#print axioms v12_hodge_L2_limit_of_fourThirds_limit
#print axioms v12_holderTriple_fourThirds_four_one
#print axioms v12_hodge_L2_interpolation_squared
end SMScattering.W20Full
