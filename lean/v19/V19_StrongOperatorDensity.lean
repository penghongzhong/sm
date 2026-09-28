import Mathlib

namespace SMScattering.W20Full

open Filter
open scoped Topology

/--
Uniformly bounded operators and one fixed unit-modulus scalar sequence:
strong convergence on a dense test class extends to every vector.

This formalizes the final density step in v19:lem:phase-profile-constant with
the quantifiers in the manuscript order: c_n is fixed before f.
-/
theorem v19_dense_strong_operator_extension
    {D H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : D → H) (hj : DenseRange j)
    (A : ℕ → H →L[ℂ] H) (c : ℕ → ℂ)
    (hA : ∀ n, ‖A n‖ ≤ 1)
    (hc : ∀ n, ‖c n‖ = 1)
    (hTest : ∀ d,
      Tendsto (fun n => A n (j d) - c n • j d) atTop (𝓝 0)) :
    ∀ f : H,
      Tendsto (fun n => A n f - c n • f) atTop (𝓝 0) := by
  intro f
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨d, hd⟩ := hj.exists_dist_lt f hquarter
  have hfd : ‖f - j d‖ < ε / 4 := by
    simpa [dist_eq_norm, norm_sub_rev] using hd
  have hdf : ‖j d - f‖ < ε / 4 := by
    simpa [norm_sub_rev] using hfd
  have htestNorm :
      Tendsto (fun n => ‖A n (j d) - c n • j d‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (hTest d)
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp htestNorm (ε / 4) hquarter
  refine ⟨N, ?_⟩
  intro n hn
  have hmid : ‖A n (j d) - c n • j d‖ < ε / 4 := hN n hn
  have hleft : ‖A n (f - j d)‖ ≤ ‖f - j d‖ := by
    calc
      ‖A n (f - j d)‖ ≤ ‖A n‖ * ‖f - j d‖ :=
        ContinuousLinearMap.le_opNorm (A n) (f - j d)
      _ ≤ 1 * ‖f - j d‖ :=
        mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _)
      _ = ‖f - j d‖ := one_mul _
  have hright : ‖c n • (j d - f)‖ = ‖j d - f‖ := by
    rw [norm_smul, hc n, one_mul]
  have hid :
      A n f - c n • f
        =
      A n (f - j d)
        + (A n (j d) - c n • j d)
        + c n • (j d - f) := by
    rw [map_sub, smul_sub]
    abel
  rw [hid]
  calc
    ‖A n (f - j d)
        + (A n (j d) - c n • j d)
        + c n • (j d - f)‖
      ≤ ‖A n (f - j d)‖
        + ‖A n (j d) - c n • j d‖
        + ‖c n • (j d - f)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_right (norm_add_le _ _) _)
    _ < ε := by
      rw [hright]
      linarith [hleft, hfd, hmid, hdf]

/--
A convenient corollary for unitary/isometric conjugated profile operators:
operator norm one supplies the uniform bound required above.
-/
theorem v19_isometric_dense_extension
    {D H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : D → H) (hj : DenseRange j)
    (A : ℕ → H →L[ℂ] H) (c : ℕ → ℂ)
    (hA : ∀ n f, ‖A n f‖ = ‖f‖)
    (hc : ∀ n, ‖c n‖ = 1)
    (hTest : ∀ d,
      Tendsto (fun n => A n (j d) - c n • j d) atTop (𝓝 0))
    (hOp : ∀ n, ‖A n‖ ≤ 1) :
    ∀ f : H,
      Tendsto (fun n => A n f - c n • f) atTop (𝓝 0) := by
  exact v19_dense_strong_operator_extension j hj A c hOp hc hTest

#print axioms v19_dense_strong_operator_extension
#print axioms v19_isometric_dense_extension

end SMScattering.W20Full
