import Mathlib.Tactic

/-!
Fixed-anchor support for v19:lem:phase-profile-constant.
Select the normalized mean on ONE fixed ball before choosing any test.
Actual L2 overlap and Fourier operator instances remain proof obligations.
-/

namespace SMScattering.W20Full

open Filter
open scoped Topology

noncomputable def v19_unit_phase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem v19_unit_phase_norm (z : ℂ) : ‖v19_unit_phase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [v19_unit_phase, hz]
  · rw [v19_unit_phase, if_neg hz, norm_div,
      Complex.norm_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr hz)

theorem v19_variance_controls_mean_modulus
    (r variance : ℝ) (hr : 0 ≤ r) (hv : 0 ≤ variance)
    (hid : r ^ 2 + variance = 1) :
    0 ≤ 1 - r ∧ 1 - r ≤ variance := by
  have hr1 : r ≤ 1 := by nlinarith
  have hprod : 0 ≤ r * (1 - r) := mul_nonneg hr (sub_nonneg.mpr hr1)
  constructor <;> nlinarith

theorem v19_anchor_phase_agreement
    (c d : ℕ → ℂ) (e1 eR : ℕ → ℝ) (a : ℝ)
    (ha : 0 < a)
    (hOverlap : ∀ n, a * ‖c n - d n‖ ≤ e1 n + eR n)
    (h1 : Tendsto e1 atTop (𝓝 0))
    (hR : Tendsto eR atTop (𝓝 0)) :
    Tendsto (fun n => ‖c n - d n‖) atTop (𝓝 0) := by
  have hupper : ∀ n, ‖c n - d n‖ ≤ (e1 n + eR n) / a := by
    intro n
    apply (le_div_iff₀ ha).mpr
    nlinarith [hOverlap n]
  have hzero : Tendsto (fun n => (e1 n + eR n) / a) atTop (𝓝 0) := by
    simpa using (h1.add hR).div_const a
  exact squeeze_zero (fun n => norm_nonneg _) hupper hzero

theorem v19_anchor_local_error_limit
    (c d : ℕ → ℂ) (localErr nearErr : ℕ → ℝ) (b : ℝ)
    (hNonneg : ∀ n, 0 ≤ localErr n)
    (hBound : ∀ n, localErr n ≤ nearErr n + b * ‖c n - d n‖)
    (hNear : Tendsto nearErr atTop (𝓝 0))
    (hPhase : Tendsto (fun n => ‖c n - d n‖) atTop (𝓝 0)) :
    Tendsto localErr atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
  have hzero : Tendsto (fun n => nearErr n + b * ‖c n - d n‖)
      atTop (𝓝 0) := by
    simpa using hNear.add (hconst.mul hPhase)
  exact squeeze_zero hNonneg hBound hzero


/--
Abstract density-extension inequality behind the last step of
v19:lem:phase-profile-constant.

A n is the conjugated unitary operator and c n is a unit scalar.
If fj approximates f, the error at f is bounded by twice the
approximation error plus the already controlled error at fj.
-/
theorem v19_density_extension_inequality
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : ℕ → H →L[ℂ] H) (c : ℕ → ℂ)
    (f fj : H) (n : ℕ)
    (hA : ‖A n‖ ≤ 1)
    (hc : ‖c n‖ = 1) :
    ‖A n f - c n • f‖
      ≤ 2 * ‖f - fj‖ + ‖A n fj - c n • fj‖ := by
  have hAerr : ‖A n (f - fj)‖ ≤ ‖f - fj‖ := by
    calc
      ‖A n (f - fj)‖ ≤ ‖A n‖ * ‖f - fj‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f - fj‖ := by
        exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ = ‖f - fj‖ := one_mul _
  have hcerr : ‖c n • (f - fj)‖ = ‖f - fj‖ := by
    rw [norm_smul, hc, one_mul]
  have hid :
      A n f - c n • f =
        A n (f - fj) + (A n fj - c n • fj) - c n • (f - fj) := by
    rw [map_sub, smul_sub]
    abel
  calc
    ‖A n f - c n • f‖
        = ‖A n (f - fj) + (A n fj - c n • fj) - c n • (f - fj)‖ := by
            rw [hid]
    _ ≤ ‖A n (f - fj) + (A n fj - c n • fj)‖
          + ‖c n • (f - fj)‖ := norm_sub_le _ _
    _ ≤ (‖A n (f - fj)‖ + ‖A n fj - c n • fj‖)
          + ‖c n • (f - fj)‖ := by
            gcongr
            exact norm_add_le _ _
    _ ≤ (‖f - fj‖ + ‖A n fj - c n • fj‖) + ‖f - fj‖ := by
            rw [hcerr]
            gcongr
    _ = 2 * ‖f - fj‖ + ‖A n fj - c n • fj‖ := by ring

/--
Sequential density extension with one phase sequence chosen independently
of the approximating vector.
-/
theorem v19_density_extension_limit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : ℕ → H →L[ℂ] H) (c : ℕ → ℂ)
    (f : H) (fj : ℕ → H)
    (hfj : Tendsto fj atTop (𝓝 f))
    (hA : ∀ n, ‖A n‖ ≤ 1)
    (hc : ∀ n, ‖c n‖ = 1)
    (hDense : ∀ j,
      Tendsto (fun n => ‖A n (fj j) - c n • (fj j)‖)
        atTop (𝓝 0)) :
    Tendsto (fun n => ‖A n f - c n • f‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨J, hJ⟩ :=
    Metric.tendsto_atTop.mp hfj (ε / 6) (by linarith)
  have hfjJ : ‖f - fj J‖ < ε / 6 := by
    have hj := hJ J le_rfl
    simpa [dist_eq_norm, norm_sub_rev] using hj
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp (hDense J) (ε / 3) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn
  have hcore := hN n hn
  have hcore' : ‖A n (fj J) - c n • (fj J)‖ < ε / 3 := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hcore
  have hbound :=
    v19_density_extension_inequality A c f (fj J) n (hA n) (hc n)
  have herr : ‖A n f - c n • f‖ < ε := by
    linarith
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using herr

#print axioms v19_unit_phase_norm
#print axioms v19_variance_controls_mean_modulus
#print axioms v19_anchor_phase_agreement
#print axioms v19_anchor_local_error_limit
#print axioms v19_density_extension_inequality
#print axioms v19_density_extension_limit

end SMScattering.W20Full
