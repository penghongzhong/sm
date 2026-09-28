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


/--
Any unit-modulus phase sequence has a convergent subsequence in the unit
circle.  This is the final compactness step of v19:lem:phase-profile-constant.
-/
theorem v19_unit_phase_convergent_subsequence
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ = 1) :
    ∃ c∞ : ℂ, ‖c∞‖ = 1 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n => c (σ n)) atTop (𝓝 c∞) := by
  have hmem : ∀ n, c n ∈ Metric.sphere (0 : ℂ) 1 := by
    intro n
    simpa [Metric.mem_sphere, dist_zero_left] using hc n
  obtain ⟨c∞, hc∞, σ, hσ, hlim⟩ :=
    (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hmem
  refine ⟨c∞, ?_, σ, hσ, hlim⟩
  simpa [Metric.mem_sphere, dist_zero_left] using hc∞

#print axioms v19_unit_phase_convergent_subsequence


/--
Quantifier-closed version of the final part of v19:lem:phase-profile-constant.

One unit phase sequence c_n is fixed before the test vector.  Strong convergence
on a dense class extends to every f in H, and then compactness of S^1 gives a
single further subsequence on which the phases converge while the same strong
operator convergence remains valid for every f.
-/
theorem v19_phase_profile_quantifier_bridge
    {D H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : D → H) (hj : DenseRange j)
    (A : ℕ → H →L[ℂ] H) (c : ℕ → ℂ)
    (hA : ∀ n, ‖A n‖ ≤ 1)
    (hc : ∀ n, ‖c n‖ = 1)
    (hTest : ∀ d,
      Tendsto (fun n => A n (j d) - c n • j d) atTop (𝓝 0)) :
    ∃ (c∞ : ℂ) (σ : ℕ → ℕ),
      ‖c∞‖ = 1
        ∧ StrictMono σ
        ∧ Tendsto (fun n => c (σ n)) atTop (𝓝 c∞)
        ∧ ∀ f : H,
          Tendsto
            (fun n => A (σ n) f - c (σ n) • f)
            atTop (𝓝 0) := by
  have hAll :=
    v19_dense_strong_operator_extension j hj A c hA hc hTest
  obtain ⟨c∞, hc∞, σ, hσ, hcLim⟩ :=
    v19_unit_phase_convergent_subsequence c hc
  refine ⟨c∞, σ, hc∞, hσ, hcLim, ?_⟩
  intro f
  exact (hAll f).comp hσ.tendsto_atTop

#print axioms v19_phase_profile_quantifier_bridge

#print axioms v19_dense_strong_operator_extension
#print axioms v19_isometric_dense_extension

end SMScattering.W20Full
