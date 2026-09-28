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


/--
Moving-vector version used in both the bounded-time and pseudo-conformal
branches: uniform operator norm one plus a unit scalar lets convergence on the
limit vector transfer to a convergent sequence of test vectors.
-/
theorem v19_moving_vector_extension_inequality
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : ℕ → H →L[ℂ] H) (c : ℕ → ℂ)
    (v : ℕ → H) (vstar : H) (n : ℕ)
    (hA : ‖A n‖ ≤ 1)
    (hc : ‖c n‖ = 1) :
    ‖A n (v n) - c n • v n‖
      ≤ 2 * ‖v n - vstar‖
        + ‖A n vstar - c n • vstar‖ := by
  exact v19_density_extension_inequality
    A c (v n) vstar n hA hc

theorem v19_moving_vector_extension_limit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : ℕ → H →L[ℂ] H) (c : ℕ → ℂ)
    (v : ℕ → H) (vstar : H)
    (hv : Tendsto v atTop (𝓝 vstar))
    (hA : ∀ n, ‖A n‖ ≤ 1)
    (hc : ∀ n, ‖c n‖ = 1)
    (hstar :
      Tendsto (fun n => ‖A n vstar - c n • vstar‖)
        atTop (𝓝 0)) :
    Tendsto (fun n => ‖A n (v n) - c n • v n‖)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N1, hN1⟩ :=
    Metric.tendsto_atTop.mp hv (ε / 6) (by linarith)
  obtain ⟨N2, hN2⟩ :=
    Metric.tendsto_atTop.mp hstar (ε / 3) (by linarith)
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have hvn := hN1 n (le_trans (Nat.le_max_left _ _) hn)
  have hsn := hN2 n (le_trans (Nat.le_max_right _ _) hn)
  have hvn' : ‖v n - vstar‖ < ε / 6 := by
    simpa [dist_eq_norm] using hvn
  have hsn' : ‖A n vstar - c n • vstar‖ < ε / 3 := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hsn
  have hbound :=
    v19_moving_vector_extension_inequality
      A c v vstar n (hA n) (hc n)
  have herr : ‖A n (v n) - c n • v n‖ < ε := by
    linarith
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using herr

#print axioms v19_unit_phase_norm
#print axioms v19_variance_controls_mean_modulus
#print axioms v19_anchor_phase_agreement
#print axioms v19_anchor_local_error_limit
#print axioms v19_density_extension_inequality
#print axioms v19_density_extension_limit
#print axioms v19_moving_vector_extension_inequality
#print axioms v19_moving_vector_extension_limit


/--
Strong convergence with one phase sequence chosen before the test vector.

If the conjugated operators are uniformly contractive, |c_n|=1, and
A_n(j d)-c_n j d -> 0 on one dense test class j(D), then the same fixed
sequence c_n works for every f in H.
-/
theorem v19_fixed_phase_dense_class_extension
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
    simpa [dist_eq_norm] using hd
  have hTestNorm :
      Tendsto (fun n => ‖A n (j d) - c n • j d‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (hTest d)
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp hTestNorm (ε / 4) hquarter
  refine ⟨N, ?_⟩
  intro n hn
  have hcoreDist := hN n hn
  have hcore : ‖A n (j d) - c n • j d‖ < ε / 4 := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hcoreDist
  have hbound :=
    v19_density_extension_inequality A c f (j d) n (hA n) (hc n)
  have herr : ‖A n f - c n • f‖ < ε := by
    linarith
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using herr

/-- Unit phases admit a convergent subsequence on the compact unit circle. -/
theorem v19_unit_phase_convergent_subsequence
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ = 1) :
    ∃ cLim : ℂ, ‖cLim‖ = 1 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n => c (σ n)) atTop (𝓝 cLim) := by
  have hmem : ∀ n, c n ∈ Metric.sphere (0 : ℂ) 1 := by
    intro n
    simpa [Metric.mem_sphere, dist_zero_left] using hc n
  obtain ⟨cLim, hcLim, σ, hσ, hlim⟩ :=
    (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hmem
  refine ⟨cLim, ?_, σ, hσ, hlim⟩
  simpa [Metric.mem_sphere, dist_zero_left] using hcLim

/--
Quantifier-closed terminal bridge for v19:lem:phase-profile-constant:
one c_n is fixed before f; it works for all f; then one further subsequence
makes c_n converge without destroying any of those strong limits.
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
    ∃ (cLim : ℂ) (σ : ℕ → ℕ),
      ‖cLim‖ = 1
        ∧ StrictMono σ
        ∧ Tendsto (fun n => c (σ n)) atTop (𝓝 cLim)
        ∧ ∀ f : H,
          Tendsto
            (fun n => A (σ n) f - c (σ n) • f)
            atTop (𝓝 0) := by
  have hAll :=
    v19_fixed_phase_dense_class_extension j hj A c hA hc hTest
  obtain ⟨cLim, hcLim, σ, hσ, hcLim⟩ :=
    v19_unit_phase_convergent_subsequence c hc
  refine ⟨cLim, σ, hcLim, hσ, hcLim, ?_⟩
  intro f
  exact (hAll f).comp hσ.tendsto_atTop

#print axioms v19_fixed_phase_dense_class_extension
#print axioms v19_unit_phase_convergent_subsequence
#print axioms v19_phase_profile_quantifier_bridge


/--
The normalization estimate used after Poincare on a fixed ball.

Here d_n is the L2 error to the complex mean, r_n is the modulus of that
mean, and area is |B_R|.  The exact variance identity
  r_n^2 + d_n^2/area = 1
together with d_n -> 0 implies that the normalized unit phase has vanishing
local error whenever the manuscript triangle bound is available.
-/
theorem v19_anchor_normalization_from_variance
    (area : ℝ) (harea : 0 < area)
    (d r e : ℕ → ℝ)
    (hd0 : ∀ n, 0 ≤ d n)
    (hr0 : ∀ n, 0 ≤ r n)
    (he0 : ∀ n, 0 ≤ e n)
    (hvar : ∀ n, r n ^ 2 + (d n) ^ 2 / area = 1)
    (htri : ∀ n,
      e n ≤ d n + Real.sqrt area * (1 - r n))
    (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto e atTop (𝓝 0) := by
  let v : ℕ → ℝ := fun n => (d n) ^ 2 / area
  have hv0 : ∀ n, 0 ≤ v n := by
    intro n
    exact div_nonneg (sq_nonneg _) harea.le
  have hv : Tendsto v atTop (𝓝 0) := by
    have hsquare : Tendsto (fun n => (d n) ^ 2) atTop (𝓝 0) := by
      simpa using hd.pow 2
    simpa [v] using hsquare.div_const area
  have hr1 : ∀ n, 1 - r n ≤ v n := by
    intro n
    exact (v19_variance_controls_mean_modulus
      (r n) (v n) (hr0 n) (hv0 n) (hvar n)).2
  have hupper : ∀ n,
      e n ≤ d n + Real.sqrt area * v n := by
    intro n
    exact (htri n).trans <|
      add_le_add_left
        (mul_le_mul_of_nonneg_left (hr1 n) (Real.sqrt_nonneg area))
        (d n)
  have hzero :
      Tendsto (fun n => d n + Real.sqrt area * v n) atTop (𝓝 0) := by
    have hc :
        Tendsto (fun _ : ℕ => Real.sqrt area) atTop
          (𝓝 (Real.sqrt area)) := tendsto_const_nhds
    simpa using hd.add (hc.mul hv)
  exact squeeze_zero he0 hupper hzero

/--
One unit-ball anchor controls every larger fixed ball.

The overlap estimate gives convergence of the radius-R phase to the fixed
unit-ball phase.  The local triangle estimate then transfers the radius-R
Poincare error to the same anchor sequence.
-/
theorem v19_fixed_anchor_all_ball_limit
    (c anchorR : ℕ → ℂ)
    (e1 eR localErr : ℕ → ℝ)
    (a b : ℝ)
    (ha : 0 < a)
    (hLocal0 : ∀ n, 0 ≤ localErr n)
    (hOverlap : ∀ n,
      a * ‖c n - anchorR n‖ ≤ e1 n + eR n)
    (hLocal : ∀ n,
      localErr n ≤ eR n + b * ‖c n - anchorR n‖)
    (h1 : Tendsto e1 atTop (𝓝 0))
    (hR : Tendsto eR atTop (𝓝 0)) :
    Tendsto localErr atTop (𝓝 0) := by
  have hPhase :=
    v19_anchor_phase_agreement c anchorR e1 eR a ha hOverlap h1 hR
  exact v19_anchor_local_error_limit
    c anchorR localErr eR b hLocal0 hLocal hR hPhase

#print axioms v19_anchor_normalization_from_variance
#print axioms v19_fixed_anchor_all_ball_limit

end SMScattering.W20Full
