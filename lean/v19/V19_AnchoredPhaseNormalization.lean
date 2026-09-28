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

#print axioms v19_unit_phase_norm
#print axioms v19_variance_controls_mean_modulus
#print axioms v19_anchor_phase_agreement
#print axioms v19_anchor_local_error_limit

end SMScattering.W20Full
