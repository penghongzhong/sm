import lean.v12.V12_TimeSourceBridge
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
Weak time integration for the W20 cutoff argument.
The classical derivative below belongs to a compact spatial test curve,
NOT to the untruncated cutoff field. A weak residual is identified a.e.;
its interval identity then passes through genuine L1 source convergence.
Actual compact test construction, its PDE residual, and cutoff-kernel
approximation still require their concrete manuscript instances.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal ContDiff

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Fundamental lemma applied to the actual vector-valued residual. -/
theorem v12_weak_residual_ae_eq (a b : ℝ) (d g : ℝ → E)
    (hd : LocallyIntegrableOn d (Set.Ioo a b) volume)
    (hg : LocallyIntegrableOn g (Set.Ioo a b) volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo a b → ∫ τ : ℝ, φ τ • (d τ - g τ) = 0) :
    ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioo a b → d τ = g τ := by
  have hzero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hd.sub hg) (by
      intro φ hφ hc hs
      simpa only [Pi.sub_apply] using hweak φ hφ hc hs)
  filter_upwards [hzero] with τ hτ
  intro hmem
  exact sub_eq_zero.mp (hτ hmem)

/-- Compact-test FTC: distributional source identification suffices.
No pointwise equality of the source and the classical derivative is assumed. -/
theorem v12_compact_test_time_identity (a b : ℝ) (v d g : ℝ → E)
    (hd : LocallyIntegrableOn d (Set.Ioo a b) volume)
    (hg : LocallyIntegrableOn g (Set.Ioo a b) volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo a b → ∫ τ : ℝ, φ τ • (d τ - g τ) = 0)
    (hclassical : ∀ τ ∈ Set.Icc a b, HasDerivAt v (d τ) τ)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hst : s ≤ t) (hint : IntervalIntegrable g volume s t) :
    v t - v s = ∫ τ in s..t, g τ := by
  have hae := v12_weak_residual_ae_eq a b d g hd hg hweak
  have heq : d =ᵐ[(volume : Measure ℝ).restrict (Set.Ioo s t)] g := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae] with τ hτ
    intro hmem
    exact hτ ⟨hs.1.trans_lt hmem.1, hmem.2.trans_le ht.2⟩
  have hsets : Set.Ioo s t =ᵐ[(volume : Measure ℝ)] Set.Ioc s t :=
    Ioo_ae_eq_Ioc
  rw [Measure.restrict_congr_set hsets] at heq
  have hg' : Integrable g ((volume : Measure ℝ).restrict (Set.Ioc s t)) := by
    simpa only [intervalIntegrable_iff, Set.uIoc_of_le hst] using hint
  have hd' : IntervalIntegrable d volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [Set.uIoc_of_le hst]
    exact hg'.congr heq.symm
  have hder' : ∀ τ ∈ Set.uIcc s t, HasDerivAt v (d τ) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le hst] at hτ
    exact hclassical τ ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩
  calc
    v t - v s = ∫ τ in s..t, d τ :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt hder' hd').symm
    _ = ∫ τ in s..t, g τ := by
      rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
      exact integral_congr_ae heq

/-- Norm-L1 convergence implies convergence of the actual Bochner integrals. -/
theorem v12_integral_tendsto_of_norm_L1 (μ : Measure ℝ) (g : ℝ → E)
    (gR : ℕ → ℝ → E) (hg : Integrable g μ)
    (hR : ∀ R, Integrable (gR R) μ)
    (hL1 : Tendsto (fun R => ∫ τ, ‖gR R τ - g τ‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun R => ∫ τ, gR R τ ∂μ) atTop (𝓝 (∫ τ, g τ ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun R => norm_nonneg _) _ hL1
  intro R
  rw [← integral_sub (hR R) hg]
  exact norm_integral_le_integral_norm _

/-- Removal of the spatial cutoff through endpoint convergence and L1 sources. -/
theorem v12_time_identity_of_test_limit (u : ℝ → E) (g : ℝ → E)
    (uR gR : ℕ → ℝ → E) (s t : ℝ) (hst : s ≤ t)
    (hg : IntervalIntegrable g volume s t)
    (hR : ∀ R, IntervalIntegrable (gR R) volume s t)
    (hFTC : ∀ R, uR R t - uR R s = ∫ τ in s..t, gR R τ)
    (hus : Tendsto (fun R => uR R s) atTop (𝓝 (u s)))
    (hut : Tendsto (fun R => uR R t) atTop (𝓝 (u t)))
    (hL1 : Tendsto
      (fun R => ∫ τ in Set.Ioc s t, ‖gR R τ - g τ‖) atTop (𝓝 0)) :
    u t - u s = ∫ τ in s..t, g τ := by
  have hg' : Integrable g ((volume : Measure ℝ).restrict (Set.Ioc s t)) := by
    simpa only [intervalIntegrable_iff, Set.uIoc_of_le hst] using hg
  have hR' : ∀ R, Integrable (gR R)
      ((volume : Measure ℝ).restrict (Set.Ioc s t)) := by
    intro R
    simpa only [intervalIntegrable_iff, Set.uIoc_of_le hst] using hR R
  have hlim := v12_integral_tendsto_of_norm_L1
    ((volume : Measure ℝ).restrict (Set.Ioc s t)) g gR hg' hR' hL1
  have hlim' : Tendsto (fun R => ∫ τ in s..t, gR R τ) atTop
      (𝓝 (∫ τ in s..t, g τ)) := by
    simpa only [intervalIntegral.integral_of_le hst] using hlim
  have hleft : Tendsto (fun R => uR R t - uR R s) atTop
      (𝓝 (∫ τ in s..t, g τ)) := by
    simpa only [hFTC] using hlim'
  exact tendsto_nhds_unique (hut.sub hus) hleft

/-- Holder from an established time integral identity; no derivative hypothesis. -/
theorem v12_norm_increment_quarter_of_integral_identity_of_le
    (a b : ℝ) (u g : ℝ → E)
    (hg : MemLp g ((4 : ℝ≥0∞) / 3) ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : eLpNorm g ((4 : ℝ≥0∞) / 3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ C)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (hid : u t - u s = ∫ τ in s..t, g τ) :
    ‖u t - u s‖ ≤ C.toReal * (t - s) ^ ((1 : ℝ) / 4) := by
  have hsub : ((volume : Measure ℝ).restrict (Set.Ioc s t)) ≤
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
    apply Measure.restrict_mono _ le_rfl
    intro τ hτ
    exact ⟨hs.1.trans hτ.1.le, hτ.2.trans ht.2⟩
  have hlocal := MemLp.mono_measure hsub hg
  have hnorm : ‖∫ τ in s..t, g τ‖ₑ ≤
      C * ENNReal.ofReal (t - s) ^ ((1 : ℝ) / 4) := by
    refine (v12_enorm_intervalIntegral_le_fourThirds_quarter_of_le
      g hst hlocal.aestronglyMeasurable).trans ?_
    exact mul_le_mul' ((eLpNorm_mono_measure g hsub).trans hbound) le_rfl
  have hfinite : C * ENNReal.ofReal (t - s) ^ ((1 : ℝ) / 4) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfinite hnorm
  rw [← hid] at hreal
  simpa only [toReal_enorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] using hreal

end Banach

/-- Pointwise compact-test identities identify the same BCF-valued integral.
There is no interchange of an uncountable family of a.e. exceptional sets. -/
theorem v12_BCF_time_identity_of_pointwise (u g : ℝ → V12BCF) (s t : ℝ)
    (hg : IntervalIntegrable g volume s t)
    (hid : ∀ x : V12Spatial, u t x - u s x = ∫ τ in s..t, g τ x) :
    u t - u s = ∫ τ in s..t, g τ := by
  ext x
  change u t x - u s x = (∫ τ in s..t, g τ) x
  calc
    u t x - u s x = ∫ τ in s..t, g τ x := hid x
    _ = (∫ τ in s..t, g τ) x := by
      exact (BoundedContinuousFunction.evalCLM ℝ x).intervalIntegral_comp_comm hg

#print axioms v12_weak_residual_ae_eq
#print axioms v12_compact_test_time_identity
#print axioms v12_integral_tendsto_of_norm_L1
#print axioms v12_time_identity_of_test_limit
#print axioms v12_norm_increment_quarter_of_integral_identity_of_le
#print axioms v12_BCF_time_identity_of_pointwise

end SMScattering.W20Full
