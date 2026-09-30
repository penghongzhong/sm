import lean.v12.V12_YHodgeInterpolation

/-! The two-stage near/far limit argument in an actual normed space. The
Hodge application must provide the proved same-field approximation error. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter
open scoped Topology

theorem v12_limit_zero_from_uniform_approximants
    {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (g : ℕ → ℕ → E) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hnear : ∀ k, Tendsto (g k) atTop (𝓝 0))
    (herr : ∀ k n, ‖f n - g k n‖ ≤ δ k) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hd := (tendsto_order.mp hδ).2 (ε/2) (by positivity)
  obtain ⟨k, hk⟩ := hd.exists
  have hg := Metric.tendsto_nhds.mp (hnear k) (ε/2) (by positivity)
  filter_upwards [hg] with n hn
  simp only [dist_zero_right] at hn ⊢
  have hb := norm_le_norm_sub_add (f n) (g k n)
  have he := herr k n
  linarith

#print axioms v12_limit_zero_from_uniform_approximants
end SMScattering.W20Full
