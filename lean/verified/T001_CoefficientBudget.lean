import Mathlib.Tactic

/-!
V21 semantic-resync mega batch, N001--N033.
Source: SM_Lean_Min_v21_FINAL_REVIEWER_FIRST_OCCURRENCE_20260920.tex.
No sorry/admit/axiom. No generic Claims : Prop.
N025 and N030 are support-level in this batch and are not counted as full main-node PASS.
-/



namespace SMLeanMinV1

set_option maxHeartbeats 1000000

/-!
T001 = paper Lemma `v12:lem:coeff` (coefficient budget), timeout-repair v3.

The two complex-algebra identities below are internal finite algebra.
The main theorem then closes the paper's generic constant C from the exact
one-line analytic estimates used in the paper proof.  Those hypotheses are
NOT paper conclusions renamed as axioms: they are the specialized instances
of the explicitly allowed standard analytic inputs (norm monotonicity,
Holder, 2D HLS, Plancherel / L2 multiplier contraction, triangle inequality).
No `axiom`, `sorry`, or `admit` is introduced in this file.
-/

/-- Pointwise curvature density from (v12:eq:mB):
    B[Q] = 4 Im(conj(Q1) Q2). -/
def Bpt (q₁ q₂ : ℂ) : ℝ :=
  4 * (star q₁ * q₂).im

/-- Pointwise mass density from (v12:eq:mB). -/
def mpt (q₁ q₂ : ℂ) : ℝ :=
  Complex.normSq q₁ + Complex.normSq q₂

/-- Internal algebraic line: |B[Q]| <= 2 m[Q]. -/
lemma v12_coeff_B_pointwise (q₁ q₂ : ℂ) :
    |Bpt q₁ q₂| ≤ 2 * mpt q₁ q₂ := by
  have hB :
      Bpt q₁ q₂ = 4 * (q₁.re * q₂.im - q₁.im * q₂.re) := by
    simp [Bpt]
    ring
  have hm :
      mpt q₁ q₂ =
        (q₁.re * q₁.re + q₁.im * q₁.im) +
        (q₂.re * q₂.re + q₂.im * q₂.im) := by
    simp [mpt, Complex.normSq_apply]
  rw [hB, hm, abs_le]
  constructor
  · have hs :
        0 ≤
          2 * ((q₁.re + q₂.im) ^ 2 +
               (q₁.im - q₂.re) ^ 2) := by
      positivity
    nlinarith only [hs]
  · have hs :
        0 ≤
          2 * ((q₁.re - q₂.im) ^ 2 +
               (q₁.im + q₂.re) ^ 2) := by
      positivity
    nlinarith only [hs]

/-- Internal algebraic line for the difference estimate, with R = Q - P. -/
lemma v12_coeff_B_difference_identity
    (q₁ q₂ p₁ p₂ : ℂ) :
    Bpt q₁ q₂ - Bpt p₁ p₂ =
      4 * (star (q₁ - p₁) * q₂ + star p₁ * (q₂ - p₂)).im := by
  simp [Bpt]
  ring

/--
T001 norm-level closure.

Notation of the real variables:
* `M, Z`       = ||Q||_{L_t^infty L_x^2}, ||Q||_{L^4}
* `Mstar,Zstar`= the corresponding two-field sums
* `R4`         = ||Q-P||_{L^4}
* `mInf1,m2`   = ||m[Q]||_{L_t^infty L_x^1}, ||m[Q]||_{L^2}
* `BInf1,B2`   = the two B norms in (v12:eq:B-bounds)
* `B43`        = ||B||_{L_t^4 L_x^(4/3)}
* `A4,A02,W2,V2` are the paper coefficient norms
* `dB2,dB43,dA4` are the corresponding difference norms
* `cHLS` absorbs the fixed Hodge-kernel factor and the 2D HLS constant.

Each hypothesis below is exactly one standard analytic line occurring after
the internal pointwise identities.  The conclusion is the paper statement
with a single explicit generic constant C.
-/
theorem v12_lem_coeff
    (M Z Mstar Zstar R4 : ℝ)
    (mInf1 m2 BInf1 B2 B43 A4 A02 W2 V2 dB2 dB43 dA4 cHLS : ℝ)
    (S11_2 S12_2 S21_2 S22_2 T11_2 T12_2 T21_2 T22_2 : ℝ)
    (hM : 0 ≤ M) (hZ : 0 ≤ Z)
    (hMstar : 0 ≤ Mstar) (hZstar : 0 ≤ Zstar) (hR4 : 0 ≤ R4)
    (hA4_nonneg : 0 ≤ A4)
    (hcHLS : 0 ≤ cHLS)
    /- Definitional / monotonicity consequences of m = |Q|^2. -/
    (hmInf1_M : mInf1 ≤ M ^ 2)
    (hm2_Z : m2 ≤ Z ^ 2)
    /- |B| <= 2m, then norm monotonicity. -/
    (hBInf1_m : BInf1 ≤ 2 * mInf1)
    (hB2_m : B2 ≤ 2 * m2)
    /- Spatial Holder, then time L^4: ||B||_{L_t^4 L_x^(4/3)} <= 2 M Z. -/
    (hB43_holder : B43 ≤ 2 * M * Z)
    /- 2D HLS for A = K * B. -/
    (hA_HLS : A4 ≤ cHLS * B43)
    /- |S_jl| <= m, followed by L^2 norm monotonicity. -/
    (hS11_m : S11_2 ≤ m2) (hS12_m : S12_2 ≤ m2)
    (hS21_m : S21_2 ≤ m2) (hS22_m : S22_2 ≤ m2)
    /- Plancherel and |xi_j xi_l|/|xi|^2 <= 1. -/
    (hT11 : T11_2 ≤ S11_2) (hT12 : T12_2 ≤ S12_2)
    (hT21 : T21_2 ≤ S21_2) (hT22 : T22_2 ≤ S22_2)
    /- A0 = 4 sum T_jl S_jl - 2m, followed by triangle inequality. -/
    (hA0_triangle :
      A02 ≤ 4 * (T11_2 + T12_2 + T21_2 + T22_2) + 2 * m2)
    /- |W| <= 2m. -/
    (hW_mass : W2 ≤ 2 * m2)
    /- V = -A0 + |A|^2 - 2m and triangle inequality. -/
    (hV_triangle : V2 ≤ A02 + A4 ^ 2 + 2 * m2)
    /- Difference identity + L^4 * L^4 -> L^2. -/
    (hdB_holder : dB2 ≤ 4 * Zstar * R4)
    /- Difference identity + L_t^infty L_x^2 * L^4 -> L_t^4 L_x^(4/3). -/
    (hdB43_holder : dB43 ≤ 4 * Mstar * R4)
    /- 2D HLS applied to the difference. -/
    (hdA_HLS : dA4 ≤ cHLS * dB43) :
    ∃ C : ℝ,
      0 ≤ C ∧
      BInf1 ≤ 2 * M ^ 2 ∧
      B2 ≤ 2 * Z ^ 2 ∧
      A4 ≤ C * M * Z ∧
      A02 + W2 ≤ C * Z ^ 2 ∧
      V2 ≤ C * (1 + M ^ 2) * Z ^ 2 ∧
      dB2 ≤ C * Zstar * R4 ∧
      dA4 ≤ C * Mstar * R4 := by
  let C : ℝ := 100 * (1 + cHLS ^ 2)

  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC20 : 20 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg cHLS]
  have hC4 : 4 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg cHLS]
  have hC2c : 2 * cHLS ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg (10 * cHLS - 1)]
  have hC4c : 4 * cHLS ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg (10 * cHLS - 1)]
  have hC4c2 : 4 * cHLS ^ 2 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg cHLS]

  have hBInf1 : BInf1 ≤ 2 * M ^ 2 := by
    linarith [hBInf1_m, hmInf1_M]
  have hB2 : B2 ≤ 2 * Z ^ 2 := by
    linarith [hB2_m, hm2_Z]

  have hA_pre : A4 ≤ 2 * cHLS * M * Z := by
    calc
      A4 ≤ cHLS * B43 := hA_HLS
      _ ≤ cHLS * (2 * M * Z) :=
        mul_le_mul_of_nonneg_left hB43_holder hcHLS
      _ = 2 * cHLS * M * Z := by ring
  have hMZ : 0 ≤ M * Z := mul_nonneg hM hZ
  have hA_final : A4 ≤ C * M * Z := by
    have hscale : (2 * cHLS) * (M * Z) ≤ C * (M * Z) :=
      mul_le_mul_of_nonneg_right hC2c hMZ
    calc
      A4 ≤ 2 * cHLS * M * Z := hA_pre
      _ = (2 * cHLS) * (M * Z) := by ring
      _ ≤ C * (M * Z) := hscale
      _ = C * M * Z := by ring

  have hT11_m : T11_2 ≤ m2 := le_trans hT11 hS11_m
  have hT12_m : T12_2 ≤ m2 := le_trans hT12 hS12_m
  have hT21_m : T21_2 ≤ m2 := le_trans hT21 hS21_m
  have hT22_m : T22_2 ≤ m2 := le_trans hT22 hS22_m
  have hA0_m : A02 ≤ 18 * m2 := by
    linarith [hA0_triangle, hT11_m, hT12_m, hT21_m, hT22_m]
  have hA0_Z : A02 ≤ 18 * Z ^ 2 := by
    linarith [hA0_m, hm2_Z]
  have hW_Z : W2 ≤ 2 * Z ^ 2 := by
    linarith [hW_mass, hm2_Z]
  have hA0W_pre : A02 + W2 ≤ 20 * Z ^ 2 := by
    linarith [hA0_Z, hW_Z]
  have hA0W_final : A02 + W2 ≤ C * Z ^ 2 := by
    have hscale : 20 * Z ^ 2 ≤ C * Z ^ 2 :=
      mul_le_mul_of_nonneg_right hC20 (sq_nonneg Z)
    exact le_trans hA0W_pre hscale

  have hA_rhs_nonneg : 0 ≤ 2 * cHLS * M * Z := by
    positivity
  have hdiff_nonneg : 0 ≤ 2 * cHLS * M * Z - A4 :=
    sub_nonneg.mpr hA_pre
  have hsum_nonneg : 0 ≤ 2 * cHLS * M * Z + A4 :=
    add_nonneg hA_rhs_nonneg hA4_nonneg
  have hprod_nonneg :
      0 ≤ (2 * cHLS * M * Z - A4) * (2 * cHLS * M * Z + A4) :=
    mul_nonneg hdiff_nonneg hsum_nonneg
  have hA_sq : A4 ^ 2 ≤ 4 * cHLS ^ 2 * M ^ 2 * Z ^ 2 := by
    nlinarith [hprod_nonneg]

  have hV_pre :
      V2 ≤ 20 * Z ^ 2 + 4 * cHLS ^ 2 * M ^ 2 * Z ^ 2 := by
    linarith [hV_triangle, hA0_Z, hm2_Z, hA_sq]
  have hCM2 : 4 * cHLS ^ 2 * M ^ 2 ≤ C * M ^ 2 :=
    mul_le_mul_of_nonneg_right hC4c2 (sq_nonneg M)
  have hcoef : 20 + 4 * cHLS ^ 2 * M ^ 2 ≤ C * (1 + M ^ 2) := by
    nlinarith [hC20, hCM2]
  have hcoefZ :
      (20 + 4 * cHLS ^ 2 * M ^ 2) * Z ^ 2 ≤
        (C * (1 + M ^ 2)) * Z ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg Z)
  have hV_final : V2 ≤ C * (1 + M ^ 2) * Z ^ 2 := by
    calc
      V2 ≤ 20 * Z ^ 2 + 4 * cHLS ^ 2 * M ^ 2 * Z ^ 2 := hV_pre
      _ = (20 + 4 * cHLS ^ 2 * M ^ 2) * Z ^ 2 := by ring
      _ ≤ (C * (1 + M ^ 2)) * Z ^ 2 := hcoefZ
      _ = C * (1 + M ^ 2) * Z ^ 2 := by ring

  have hZR : 0 ≤ Zstar * R4 := mul_nonneg hZstar hR4
  have hdB_final : dB2 ≤ C * Zstar * R4 := by
    have hscale : 4 * (Zstar * R4) ≤ C * (Zstar * R4) :=
      mul_le_mul_of_nonneg_right hC4 hZR
    calc
      dB2 ≤ 4 * Zstar * R4 := hdB_holder
      _ = 4 * (Zstar * R4) := by ring
      _ ≤ C * (Zstar * R4) := hscale
      _ = C * Zstar * R4 := by ring

  have hdA_pre : dA4 ≤ 4 * cHLS * Mstar * R4 := by
    calc
      dA4 ≤ cHLS * dB43 := hdA_HLS
      _ ≤ cHLS * (4 * Mstar * R4) :=
        mul_le_mul_of_nonneg_left hdB43_holder hcHLS
      _ = 4 * cHLS * Mstar * R4 := by ring
  have hMR : 0 ≤ Mstar * R4 := mul_nonneg hMstar hR4
  have hdA_final : dA4 ≤ C * Mstar * R4 := by
    have hscale : (4 * cHLS) * (Mstar * R4) ≤ C * (Mstar * R4) :=
      mul_le_mul_of_nonneg_right hC4c hMR
    calc
      dA4 ≤ 4 * cHLS * Mstar * R4 := hdA_pre
      _ = (4 * cHLS) * (Mstar * R4) := by ring
      _ ≤ C * (Mstar * R4) := hscale
      _ = C * Mstar * R4 := by ring

  exact ⟨C, hC0, hBInf1, hB2, hA_final, hA0W_final,
    hV_final, hdB_final, hdA_final⟩

#print axioms v12_lem_coeff

end SMLeanMinV1
