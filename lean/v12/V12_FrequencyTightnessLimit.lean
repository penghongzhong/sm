import Mathlib.Tactic

/-!
A metric-space limit lemma for the last step of v12:thm:tightness.
Uniform approximation by Cauchy sequences with vanishing cutoff error
implies convergence in a complete metric space. Target Cauchyness or
convergence is not assumed.

Still required for W20: actual local L2 instantiation, one common extracted
subsequence, and proofs of its concrete cutoff hypotheses.
-/

namespace SMScattering.W20Full

open Filter
open scoped Topology

theorem v12_cauchy_of_uniform_cutoff
    {X : Type*} [MetricSpace X]
    (u : ℕ → X) (v : ℕ → ℕ → X) (err : ℕ → ℝ)
    (hErr : Tendsto err atTop (𝓝 0))
    (hApprox : ∀ k n, dist (u n) (v k n) ≤ err k)
    (hCutoff : ∀ k, CauchySeq (v k)) :
    CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hErr (ε / 3) hthird
  have habs : |err k| < ε / 3 := by
    simpa [Real.dist_eq] using hk k le_rfl
  have he : err k < ε / 3 := lt_of_le_of_lt (le_abs_self _) habs
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hCutoff k) (ε / 3) hthird
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmiddle : dist (v k m) (v k n) < ε / 3 := hN m hm n hn
  have hleft := hApprox k m
  have hright : dist (v k n) (u n) ≤ err k := by
    rw [dist_comm]
    exact hApprox k n
  have ht1 := dist_triangle (u m) (v k m) (u n)
  have ht2 := dist_triangle (v k m) (v k n) (u n)
  linarith

theorem v12_limit_of_uniform_cutoff
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (u : ℕ → X) (v : ℕ → ℕ → X) (err : ℕ → ℝ)
    (hErr : Tendsto err atTop (𝓝 0))
    (hApprox : ∀ k n, dist (u n) (v k n) ≤ err k)
    (hCutoff : ∀ k, CauchySeq (v k)) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  exact cauchySeq_tendsto_of_complete
    (v12_cauchy_of_uniform_cutoff u v err hErr hApprox hCutoff)

#print axioms v12_cauchy_of_uniform_cutoff
#print axioms v12_limit_of_uniform_cutoff

end SMScattering.W20Full
