import lean.v12.V12_YNonlinearLocalProducts

/-! Dense-test extension under actual operator norm bounds. The concrete
density and compact-test limit for reconstructed coefficients are not assumed
by the full-paper theorem: they remain separately tracked obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open Filter
open scoped Topology

theorem v12_dense_test_extension
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Tn : ℕ → E →L[ℂ] F) (T : E →L[ℂ] F)
    (C : ℝ) (hC : ∀ n, ‖Tn n‖ ≤ C)
    (D : Set E) (hD : Dense D)
    (hlim : ∀ y ∈ D, Tendsto (fun n => Tn n y) atTop (𝓝 (T y))) :
    ∀ x, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)) := by
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hC0 : 0 ≤ C := (norm_nonneg (Tn 0)).trans (hC 0)
  let K := C + ‖T‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := ε / (2 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x hδ
  have hn := Metric.tendsto_nhds.mp (hlim y hyD) (ε / 2) (by positivity)
  filter_upwards [hn] with n hn
  have h1 : dist (Tn n x) (Tn n y) ≤ C * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((Tn n).le_opNorm (x-y)).trans
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  have h2 : dist (T y) (T x) ≤ ‖T‖ * dist x y := by
    rw [dist_comm (T y), dist_eq_norm, dist_eq_norm, ← map_sub]
    exact T.le_opNorm (x-y)
  have hb : (C + ‖T‖) * dist x y < ε / 2 := by
    have he : K * δ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hK]
    have hh : (C + ‖T‖) * dist x y ≤ K * dist x y := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      dsimp [K]
      linarith
    exact (hh.trans_lt (mul_lt_mul_of_pos_left hxy hK)).trans_eq he
  have ht := dist_triangle (Tn n x) (Tn n y) (T x)
  have hu := dist_triangle (Tn n y) (T y) (T x)
  nlinarith

#print axioms v12_dense_test_extension
end SMScattering.W20Full
