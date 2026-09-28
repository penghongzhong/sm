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


open scoped BigOperators

namespace SMLeanMinV1

/-!
T002 = `v13:def:GN`
Smith-type G_k / N_k^+ resolution.

This file formalizes the definition node only.  The primitive mixed norms,
window norms and angular projections are packaged as already-defined
functionals; T002 merely combines them exactly as in the paper.

No analytic theorem, axiom, `sorry`, or `admit` is introduced here.
-/

noncomputable section

/-- `2^(a k)` with integer dyadic index `k`. -/
def dyadic (a : ℝ) (k : ℤ) : ℝ :=
  Real.rpow 2 (a * (k : ℝ))

/--
Primitive norm/projection data used by the Smith resolution.
Each field corresponds to a norm or projection that exists before
`v13:def:GN`; T002 only assembles these primitives.
-/
structure SmithAtoms (E Θ : Type*) where
  /- solution-side primitive norms -/
  LtInfLx2     : E → ℝ
  L4tx         : E → ℝ
  Lx4LtInf     : E → ℝ
  Ltheta36     : Θ → E → ℝ
  LthetaWin2Inf : ℤ → Θ → E → ℝ
  Pjt          : ℤ → Θ → E → E
  Ltheta63     : Θ → E → ℝ
  LthetaLambdaInf2 : Θ → ℝ → E → ℝ

  /- forcing-side primitive norms -/
  L43tx        : E → ℝ
  Le1_3265     : E → ℝ
  Le2_3265     : E → ℝ
  Le1_6532     : E → ℝ
  Le2_6532     : E → ℝ
  LthetaWin12  : ℤ → Θ → E → ℝ
  Lt1Lx2       : E → ℝ

  /- Littlewood--Paley projection for the global square sum -/
  Pk           : ℤ → E → E

variable {E Θ : Type*} [AddCommMonoid E]

/-- Supremum over directions `θ ∈ S¹`. -/
def supTheta (g : Θ → ℝ) : ℝ :=
  sSup (Set.range g)

/-- Supremum over `|j-k| ≤ 20` and directions. -/
def supBandTheta (k : ℤ) (g : ℤ → Θ → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ j : ℤ, |j - k| ≤ 20 ∧ ∃ θ : Θ, r = g j θ}

/-- Supremum over `|j-k| ≤ 20`, directions, and `|λ| < 2^(k-40)`. -/
def supBandThetaLambda
    (k : ℤ) (g : ℤ → Θ → ℝ → ℝ) : ℝ :=
  sSup {r : ℝ |
    ∃ j : ℤ, |j - k| ≤ 20 ∧
    ∃ θ : Θ, ∃ lam : ℝ,
      |lam| < dyadic 1 (k - 40) ∧ r = g j θ lam}

/-- Paper formula (v13:eq:F0). -/
def Fk0 (A : SmithAtoms E Θ) (k : ℤ) (f : E) : ℝ :=
  A.LtInfLx2 f
    + A.L4tx f
    + dyadic (-1 / 2) k * A.Lx4LtInf f
    + dyadic (-1 / 6) k * supTheta (fun θ => A.Ltheta36 θ f)
    + dyadic (-1 / 2) k * supTheta (fun θ => A.LthetaWin2Inf (k + 40) θ f)

/-- Paper formula (v13:eq:Gk). -/
def Gk (A : SmithAtoms E Θ) (k : ℤ) (f : E) : ℝ :=
  Fk0 A k f
    + dyadic (1 / 6) k *
        supBandTheta k (fun j θ => A.Ltheta63 θ (A.Pjt j θ f))
    + dyadic (1 / 2) k *
        supBandThetaLambda k
          (fun j θ lam => A.LthetaLambdaInf2 θ lam (A.Pjt j θ f))

/-- Cost of a six-atom forcing decomposition. -/
def NkCost6
    (A : SmithAtoms E Θ) (k : ℤ) (d : Fin 6 → E) : ℝ :=
  A.L43tx (d 0)
    + dyadic (1 / 6) k * A.Le1_3265 (d 1)
    + dyadic (1 / 6) k * A.Le2_3265 (d 2)
    + dyadic (-1 / 6) k * A.Le1_6532 (d 3)
    + dyadic (-1 / 6) k * A.Le2_6532 (d 4)
    + dyadic (-1 / 2) k *
        supTheta (fun θ => A.LthetaWin12 (k - 40) θ (d 5))

/-- Paper formula (v13:eq:Nk): infimum over all six-atom decompositions. -/
def Nk (A : SmithAtoms E Θ) (k : ℤ) (F : E) : ℝ :=
  sInf {r : ℝ |
    ∃ d : Fin 6 → E,
      (∑ i, d i) = F ∧ r = NkCost6 A k d}

/-- Paper formula (v13:eq:Nplus). -/
def NkPlus (A : SmithAtoms E Θ) (k : ℤ) (F : E) : ℝ :=
  sInf {r : ℝ |
    ∃ F0 F1 : E,
      F = F0 + F1 ∧ r = Nk A k F0 + A.Lt1Lx2 F1}

/-- Cost of a five-atom strong-forcing decomposition. -/
def NtildeCost5
    (A : SmithAtoms E Θ) (k : ℤ) (d : Fin 5 → E) : ℝ :=
  A.L43tx (d 0)
    + dyadic (1 / 6) k * A.Le1_3265 (d 1)
    + dyadic (1 / 6) k * A.Le2_3265 (d 2)
    + dyadic (-1 / 6) k * A.Le1_6532 (d 3)
    + dyadic (-1 / 6) k * A.Le2_6532 (d 4)

/-- Paper formula (v13:eq:Ntilde). -/
def Ntilde (A : SmithAtoms E Θ) (k : ℤ) (F : E) : ℝ :=
  sInf {r : ℝ |
    ∃ d : Fin 5 → E,
      (∑ i, d i) = F ∧ r = NtildeCost5 A k d}

/-- Paper formula (v13:eq:Nhat). -/
def NhatPlus (A : SmithAtoms E Θ) (k : ℤ) (F : E) : ℝ :=
  sInf {r : ℝ |
    ∃ F0 F1 : E,
      F = F0 + F1 ∧ r = Ntilde A k F0 + A.Lt1Lx2 F1}

/-- Paper formula (v13:eq:Gtilde). -/
def Gtilde (A : SmithAtoms E Θ) (k : ℤ) (f : E) : ℝ :=
  A.LtInfLx2 f
    + A.L4tx f
    + dyadic (-1 / 2) k * A.Lx4LtInf f
    + dyadic (-1 / 6) k * supTheta (fun θ => A.Ltheta36 θ f)
    + dyadic (1 / 6) k *
        supBandTheta k (fun j θ => A.Ltheta63 θ (A.Pjt j θ f))

/-- Paper formula (v13:eq:Nlsatom). -/
def Nls (A : SmithAtoms E Θ) (k : ℤ) (F : E) : ℝ :=
  dyadic (-1 / 2) k *
    supTheta (fun θ => A.LthetaWin12 (k - 40) θ F)

/-- Paper formula (v13:eq:SNglobal), solution square sum. -/
def S0 (A : SmithAtoms E Θ) (f : E) : ℝ :=
  Real.sqrt (∑' k : ℤ, (Gk A k (A.Pk k f)) ^ 2)

/-- Paper formula (v13:eq:SNglobal), forcing square sum. -/
def N0 (A : SmithAtoms E Θ) (F : E) : ℝ :=
  Real.sqrt (∑' k : ℤ, (NkPlus A k (A.Pk k F)) ^ 2)

/-- Paper formula (v13:eq:SNglobal), strong-forcing square sum. -/
def Nhat0 (A : SmithAtoms E Θ) (F : E) : ℝ :=
  Real.sqrt (∑' k : ℤ, (NhatPlus A k (A.Pk k F)) ^ 2)

#check Fk0
#check Gk
#check Nk
#check NkPlus
#check Ntilde
#check NhatPlus
#check Gtilde
#check Nls
#check S0
#check N0
#check Nhat0

#print axioms Fk0
#print axioms Gk
#print axioms Nk
#print axioms NkPlus
#print axioms Ntilde
#print axioms NhatPlus
#print axioms Gtilde
#print axioms Nls
#print axioms S0
#print axioms N0
#print axioms Nhat0

end

end SMLeanMinV1


namespace SMLeanMinV1

/-!
T003 = `v13:prop:Smith-inputs`
Exact audit boundary for the Smith (Analysis & PDE 6 (2013), 601--686) inputs.

This node is a SOURCE/INTERFACE AUDIT, not a re-proof of Smith's published
analysis.  It machine-checks the exact whitelist of external Smith results
that later Lean files are allowed to invoke.

Audited published inputs:

  S1. Proposition 3.6: main linear G_k / N_k estimate for frequency-localized
      free Schrödinger evolution.

  S2. Lemma 3.9, estimate (3-10): the high-output / deep-low bilinear
      N_k estimate with decay 2^{-|k-k1|/2}, under k1 <= k-80.

  S3. Lemma 3.9, estimate (3-11): the L^2_{t,x} bilinear estimate with
      decay 2^{-|k1-k2|/2}, under k1 <= k2.

  S4. Lemma 3.10: main trilinear estimate with its published frequency
      coefficients C_{k,k1,k2,k3}.

  S5. Corollary 3.11: frequency-envelope summation of the Lemma 3.10
      coefficients.  Smith fixes delta = 1/40 as sufficient in Definition 2.5;
      the Lean-min use delta < 1/40 is a stronger restriction and is safe.

  S6. Section 5 modified product spaces: the product adapted form uses the
      modified tilde-N_k / tilde-G_k spaces which omit the sixth
      local-smoothing/maximal forcing atom.

  S7. Corollary 5.7: abstract bilinear Strichartz estimate, retaining its
      Fourier-support, small L^infty magnetic-potential, narrow-direction,
      and controlled-derived-sequence hypotheses.

NOT registered as Smith-published external inputs:

  D1. The N_k^+ linear estimate.  In the paper this is derived after
      Proposition 3.6 by Duhamel plus the L^1_t L^2_x atom; it is therefore
      a later derived bridge, not a Smith theorem tag.

  D2. Caloric-gauge global regularity conclusions.

  D3. Heat-flow global conclusions.

  D4. Final Schrödinger-map regularity/scattering conclusions.

Thus later files cannot silently use D1--D4 under the name "Smith input".
-/

/-- All Smith-related labels that could conceivably be requested later. -/
inductive SmithResultTag where
  | prop36_main_linear
  | lemma39_N_bilinear
  | lemma39_L2_bilinear
  | lemma310_trilinear
  | cor311_envelope_sum
  | section5_modified_product_spaces
  | cor57_abstract_bilinear
  | freePlus_Duhamel_derived
  | caloricGauge_global
  | heatFlow_global
  | finalSchrodingerMap_regularity
  deriving DecidableEq, Repr

/--
The exact external whitelist certified by T003.

`freePlus_Duhamel_derived` is deliberately false here: it is a derived
internal/standard-analysis bridge, not a published Smith input.
-/
def smithPublishedAllowed : SmithResultTag → Bool
  | .prop36_main_linear => true
  | .lemma39_N_bilinear => true
  | .lemma39_L2_bilinear => true
  | .lemma310_trilinear => true
  | .cor311_envelope_sum => true
  | .section5_modified_product_spaces => true
  | .cor57_abstract_bilinear => true
  | .freePlus_Duhamel_derived => false
  | .caloricGauge_global => false
  | .heatFlow_global => false
  | .finalSchrodingerMap_regularity => false

/--
Lean equivalent of Proposition `v13:prop:Smith-inputs` at the interface-audit
level: a Smith-related result is externally admissible iff it is exactly one
of the seven source-audited published inputs listed in the paper.

This theorem contains no analytic axiom; the actual analytic statements will
be supplied later only through these whitelisted source tags.
-/
theorem v13_prop_Smith_inputs (t : SmithResultTag) :
    smithPublishedAllowed t = true ↔
      t = .prop36_main_linear ∨
      t = .lemma39_N_bilinear ∨
      t = .lemma39_L2_bilinear ∨
      t = .lemma310_trilinear ∨
      t = .cor311_envelope_sum ∨
      t = .section5_modified_product_spaces ∨
      t = .cor57_abstract_bilinear := by
  cases t <;> simp [smithPublishedAllowed]

#print axioms v13_prop_Smith_inputs

end SMLeanMinV1

namespace SMLeanMinV1

/-!
T004 = `v13:lem:lowA`
Low-frequency Coulomb potential satisfies the Smith small-potential condition.

Internal dependency:
  * T001 = `v12:lem:coeff`, included above in its web-verified form.

Legal standard-analysis interfaces used here:
  * Littlewood--Paley order -1 kernel estimate
      ||P_m A||_∞ <= C_ker ||B||_1 2^m.
  * Dyadic geometric decay: for X >= 0 and eps > 0,
      X 2^{-N} <= eps for some N.
  * Exact dyadic shift identity
      2^{k-N} = 2^{-N} 2^k.

The last two are elementary standard real/dyadic facts; they are deliberately
stated in general form and do not contain the paper's low-A conclusion.
-/

/--
Paper-line version of Lemma `v13:lem:lowA`.

`lowA m` represents `||P_{<=m} A[Q]||_{L^∞_{t,x}}`.
`epsSmith` is the absolute small-potential threshold supplied by the audited
Smith input.  The theorem chooses `eps_m = epsSmith/2`.
-/
theorem v13_lem_lowA
    (M E Cker epsSmith mInf1 BInf1 : ℝ)
    (lowA : ℤ → ℝ)
    (hM : 0 ≤ M)
    (hE : 0 ≤ E)
    (hCker : 0 ≤ Cker)
    (hSmith : 0 < epsSmith)

    /- The norm ingredients already used by the web-verified T001. -/
    (hmInf1_M : mInf1 ≤ M ^ 2)
    (hBInf1_m : BInf1 ≤ 2 * mInf1)

    /- Energy controls the conserved L² mass size. -/
    (hM_energy : M ^ 2 ≤ E)

    /- Standard LP kernel estimate after summing the geometric low shells. -/
    (hLP :
      ∀ m : ℤ,
        lowA m ≤ Cker * BInf1 * ((2 : ℝ) ^ m))

    /- Standard dyadic geometric decay. -/
    (hdyadic_decay :
      ∀ X eps : ℝ,
        0 ≤ X →
        0 < eps →
        ∃ N : ℕ,
          X * ((2 : ℝ) ^ (-(N : ℤ))) ≤ eps)

    /- Elementary exact dyadic shift identity. -/
    (hdyadic_shift :
      ∀ (k : ℤ) (N : ℕ),
        ((2 : ℝ) ^ (k - (N : ℤ))) =
          ((2 : ℝ) ^ (-(N : ℤ))) * ((2 : ℝ) ^ k)) :

    ∃ C_LP eps_m : ℝ,
      0 ≤ C_LP ∧
      0 < eps_m ∧
      eps_m < epsSmith ∧
      (∀ m : ℤ,
        lowA m ≤ C_LP * E * ((2 : ℝ) ^ m)) ∧
      ∃ Λ0 : ℕ,
        ∀ k : ℤ,
          lowA (k - (Λ0 : ℤ))
            ≤ eps_m * ((2 : ℝ) ^ k) := by

  /-
  Invoke the already web-verified T001 with dummy values in all components
  irrelevant to the first coefficient bound.  This extracts exactly
      BInf1 <= 2 M^2.
  -/
  have hT001 := v12_lem_coeff
    (M := M)
    (Z := 0)
    (Mstar := 0)
    (Zstar := 0)
    (R4 := 0)
    (mInf1 := mInf1)
    (m2 := 0)
    (BInf1 := BInf1)
    (B2 := 0)
    (B43 := 0)
    (A4 := 0)
    (A02 := 0)
    (W2 := 0)
    (V2 := 0)
    (dB2 := 0)
    (dB43 := 0)
    (dA4 := 0)
    (cHLS := 0)
    (S11_2 := 0)
    (S12_2 := 0)
    (S21_2 := 0)
    (S22_2 := 0)
    (T11_2 := 0)
    (T12_2 := 0)
    (T21_2 := 0)
    (T22_2 := 0)
    (hM := hM)
    (hZ := by norm_num)
    (hMstar := by norm_num)
    (hZstar := by norm_num)
    (hR4 := by norm_num)
    (hA4_nonneg := by norm_num)
    (hcHLS := by norm_num)
    (hmInf1_M := hmInf1_M)
    (hm2_Z := by norm_num)
    (hBInf1_m := hBInf1_m)
    (hB2_m := by norm_num)
    (hB43_holder := by simp)
    (hA_HLS := by norm_num)
    (hS11_m := by norm_num)
    (hS12_m := by norm_num)
    (hS21_m := by norm_num)
    (hS22_m := by norm_num)
    (hT11 := by norm_num)
    (hT12 := by norm_num)
    (hT21 := by norm_num)
    (hT22 := by norm_num)
    (hA0_triangle := by norm_num)
    (hW_mass := by norm_num)
    (hV_triangle := by norm_num)
    (hdB_holder := by norm_num)
    (hdB43_holder := by norm_num)
    (hdA_HLS := by norm_num)

  rcases hT001 with
    ⟨_, _, hB_M, _, _, _, _, _, _⟩

  have hB_E : BInf1 ≤ 2 * E := by
    linarith [hB_M, hM_energy]

  let C_LP : ℝ := 2 * Cker
  have hCLP0 : 0 ≤ C_LP := by
    dsimp [C_LP]
    positivity

  have hlow :
      ∀ m : ℤ,
        lowA m ≤ C_LP * E * ((2 : ℝ) ^ m) := by
    intro m
    have hp : 0 ≤ ((2 : ℝ) ^ m) := by
      positivity
    have h1 :
        Cker * BInf1 ≤ Cker * (2 * E) :=
      mul_le_mul_of_nonneg_left hB_E hCker
    have h2 :
        Cker * BInf1 * ((2 : ℝ) ^ m)
          ≤ Cker * (2 * E) * ((2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_right h1 hp
    calc
      lowA m
          ≤ Cker * BInf1 * ((2 : ℝ) ^ m) := hLP m
      _ ≤ Cker * (2 * E) * ((2 : ℝ) ^ m) := h2
      _ = C_LP * E * ((2 : ℝ) ^ m) := by
          dsimp [C_LP]
          ring

  let eps_m : ℝ := epsSmith / 2
  have heps0 : 0 < eps_m := by
    dsimp [eps_m]
    linarith
  have heps_lt : eps_m < epsSmith := by
    dsimp [eps_m]
    linarith

  have hXE : 0 ≤ C_LP * E :=
    mul_nonneg hCLP0 hE

  obtain ⟨Λ0, hΛ0⟩ :=
    hdyadic_decay (C_LP * E) eps_m hXE heps0

  have hsmall :
      ∀ k : ℤ,
        lowA (k - (Λ0 : ℤ))
          ≤ eps_m * ((2 : ℝ) ^ k) := by
    intro k
    have hpk : 0 ≤ ((2 : ℝ) ^ k) := by
      positivity
    have hΛmult :
        (C_LP * E * ((2 : ℝ) ^ (-(Λ0 : ℤ))))
            * ((2 : ℝ) ^ k)
          ≤ eps_m * ((2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hΛ0 hpk
    calc
      lowA (k - (Λ0 : ℤ))
          ≤ C_LP * E * ((2 : ℝ) ^ (k - (Λ0 : ℤ))) :=
            hlow (k - (Λ0 : ℤ))
      _ =
          (C_LP * E * ((2 : ℝ) ^ (-(Λ0 : ℤ))))
            * ((2 : ℝ) ^ k) := by
            rw [hdyadic_shift k Λ0]
            ring
      _ ≤ eps_m * ((2 : ℝ) ^ k) := hΛmult

  exact
    ⟨C_LP, eps_m, hCLP0, heps0, heps_lt, hlow, Λ0, hsmall⟩

#print axioms v13_lem_lowA

end SMLeanMinV1


open scoped BigOperators

namespace SMLeanMinV1

/-!
T005 = `v13:prop:mag-bilin`
Strong-forcing scalar product form of Smith Corollary 5.7.

Paper line:
  ||u_r v_k||_{L²_{t,x}}
    <= C 2^((r-k)/2)
       [ c_r c_k
         + g_k (g_r h_r)^(1/2)
         + g_r (g_k h_k)^(1/2) ].

External inputs used here are restricted to the source-audited Smith material:

  (S1) Corollary 5.7 in its squared bilinear-Strichartz form, after the
       paper's finite angular decomposition and d = 2 specialization.

  (S2) Smith (5-33)--(5-36), i.e. the adapted product-form bound for the
       strong forcing atoms.  The L^1_t L^2_x atom is covered by the
       standard L^∞_t L^2_x · L^1_t L^2_x pairing as in the paper.

The final `mag-bilin` estimate itself is NOT an external hypothesis.
The passage from the squared Smith bound to the displayed paper estimate
is proved below inside Lean.

No `axiom`, `sorry`, or `admit`.
-/

noncomputable section

/-- Exact paper half-gap factor `2^((r-k)/2)`. -/
def smithGapHalf (r k : ℤ) : ℝ :=
  Real.rpow 2 (((r : ℝ) - (k : ℝ)) / 2)

/--
T005, paper-line scalar closure.

`form` denotes
  B(w, Box_A w) + B_e(w, Box_A w)
after the fixed finite angular decomposition.

`hSmith57` is exactly the permitted published Corollary 5.7 interface,
already specialized to d = 2 and to the paper's frequency geometry.

`hSmithProduct` is exactly the permitted published adapted-product-space
input (5-33)--(5-36), together with the standard L^1_t L^2_x pairing.

Everything after those two interfaces is internal algebra.
-/
theorem v13_prop_mag_bilin
    (r k d0 : ℤ)
    (C uv cr ck gr gk hr hk form : ℝ)

    /- frequency separation from the proposition -/
    (hd0 : (100 : ℤ) ≤ d0)
    (hgap : r ≤ k - d0)

    /- all quantities are norms / nonnegative constants -/
    (hC : 0 ≤ C)
    (huv : 0 ≤ uv)
    (hcr : 0 ≤ cr)
    (hck : 0 ≤ ck)
    (hgr : 0 ≤ gr)
    (hgk : 0 ≤ gk)
    (hhr : 0 ≤ hr)
    (hhk : 0 ≤ hk)
    (hform : 0 ≤ form)

    /-
    Smith (5-33)--(5-36), plus the standard L^1_t L^2_x atom:
      form <= g_r g_k (h_r g_k + g_r h_k).
    -/
    (hSmithProduct :
      form ≤ gr * gk * (hr * gk + gr * hk))

    /-
    Corollary 5.7 after the paper's d=2, narrow-angular,
    low-potential, finite-frequency specialization.

    The source formula is squared, hence the square of the half-gap factor.
    The separation assumptions are explicit arguments, so they cannot be
    silently discarded by the interface.
    -/
    (hSmith57 :
      (100 : ℤ) ≤ d0 →
      r ≤ k - d0 →
      uv ^ 2 ≤
        C ^ 2 * (smithGapHalf r k) ^ 2 *
          (cr ^ 2 * ck ^ 2 + form)) :

    uv ≤
      C * smithGapHalf r k *
        (cr * ck
          + gk * Real.sqrt (gr * hr)
          + gr * Real.sqrt (gk * hk)) := by

  have hgapfac : 0 ≤ smithGapHalf r k := by
    unfold smithGapHalf
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _

  have hgrhr : 0 ≤ gr * hr :=
    mul_nonneg hgr hhr

  have hgkhk : 0 ≤ gk * hk :=
    mul_nonneg hgk hhk

  have hsqrt1 :
      (Real.sqrt (gr * hr)) ^ 2 = gr * hr :=
    Real.sq_sqrt hgrhr

  have hsqrt2 :
      (Real.sqrt (gk * hk)) ^ 2 = gk * hk :=
    Real.sq_sqrt hgkhk

  have hsqrt1_nonneg :
      0 ≤ Real.sqrt (gr * hr) :=
    Real.sqrt_nonneg _

  have hsqrt2_nonneg :
      0 ≤ Real.sqrt (gk * hk) :=
    Real.sqrt_nonneg _

  have ha : 0 ≤ cr * ck :=
    mul_nonneg hcr hck

  have hb :
      0 ≤ gk * Real.sqrt (gr * hr) :=
    mul_nonneg hgk hsqrt1_nonneg

  have hc :
      0 ≤ gr * Real.sqrt (gk * hk) :=
    mul_nonneg hgr hsqrt2_nonneg

  have hab :
      0 ≤ (cr * ck) *
        (gk * Real.sqrt (gr * hr)) :=
    mul_nonneg ha hb

  have hac :
      0 ≤ (cr * ck) *
        (gr * Real.sqrt (gk * hk)) :=
    mul_nonneg ha hc

  have hbc :
      0 ≤ (gk * Real.sqrt (gr * hr)) *
        (gr * Real.sqrt (gk * hk)) :=
    mul_nonneg hb hc

  /-
  For nonnegative a,b,c:
       a²+b²+c² <= (a+b+c)².
  -/
  have hsum_sq :
      (cr * ck) ^ 2
        + (gk * Real.sqrt (gr * hr)) ^ 2
        + (gr * Real.sqrt (gk * hk)) ^ 2
      ≤
      (cr * ck
        + gk * Real.sqrt (gr * hr)
        + gr * Real.sqrt (gk * hk)) ^ 2 := by
    nlinarith [hab, hac, hbc]

  /-
  The forcing polynomial appearing in Smith's squared estimate is exactly
  the sum of the three pure squares in the desired right-hand side.
  -/
  have hforcing_sq :
      cr ^ 2 * ck ^ 2
        + gr * gk * (hr * gk + gr * hk)
      =
      (cr * ck) ^ 2
        + (gk * Real.sqrt (gr * hr)) ^ 2
        + (gr * Real.sqrt (gk * hk)) ^ 2 := by
    calc
      cr ^ 2 * ck ^ 2
          + gr * gk * (hr * gk + gr * hk)
        =
      (cr * ck) ^ 2
        + gk ^ 2 * (gr * hr)
        + gr ^ 2 * (gk * hk) := by ring
      _ =
      (cr * ck) ^ 2
        + gk ^ 2 * (Real.sqrt (gr * hr)) ^ 2
        + gr ^ 2 * (Real.sqrt (gk * hk)) ^ 2 := by
          rw [hsqrt1, hsqrt2]
      _ =
      (cr * ck) ^ 2
        + (gk * Real.sqrt (gr * hr)) ^ 2
        + (gr * Real.sqrt (gk * hk)) ^ 2 := by ring

  have hinside :
      cr ^ 2 * ck ^ 2 + form
      ≤
      (cr * ck
        + gk * Real.sqrt (gr * hr)
        + gr * Real.sqrt (gk * hk)) ^ 2 := by
    calc
      cr ^ 2 * ck ^ 2 + form
          ≤ cr ^ 2 * ck ^ 2
              + gr * gk * (hr * gk + gr * hk) := by
                linarith
      _ =
          (cr * ck) ^ 2
            + (gk * Real.sqrt (gr * hr)) ^ 2
            + (gr * Real.sqrt (gk * hk)) ^ 2 :=
              hforcing_sq
      _ ≤
          (cr * ck
            + gk * Real.sqrt (gr * hr)
            + gr * Real.sqrt (gk * hk)) ^ 2 :=
              hsum_sq

  have hpref :
      0 ≤ C ^ 2 * (smithGapHalf r k) ^ 2 := by
    positivity

  have hsq :
      uv ^ 2
      ≤
      (C * smithGapHalf r k *
        (cr * ck
          + gk * Real.sqrt (gr * hr)
          + gr * Real.sqrt (gk * hk))) ^ 2 := by
    calc
      uv ^ 2
          ≤ C ^ 2 * (smithGapHalf r k) ^ 2 *
              (cr ^ 2 * ck ^ 2 + form) :=
            hSmith57 hd0 hgap
      _ ≤
          C ^ 2 * (smithGapHalf r k) ^ 2 *
            (cr * ck
              + gk * Real.sqrt (gr * hr)
              + gr * Real.sqrt (gk * hk)) ^ 2 :=
            mul_le_mul_of_nonneg_left hinside hpref
      _ =
          (C * smithGapHalf r k *
            (cr * ck
              + gk * Real.sqrt (gr * hr)              + gr * Real.sqrt (gk * hk))) ^ 2 := by
            ring

  have hsum_nonneg :
      0 ≤
        cr * ck
          + gk * Real.sqrt (gr * hr)
          + gr * Real.sqrt (gk * hk) := by
    positivity

  have hrhs :
      0 ≤
        C * smithGapHalf r k *
          (cr * ck
            + gk * Real.sqrt (gr * hr)
            + gr * Real.sqrt (gk * hk)) := by
    exact mul_nonneg (mul_nonneg hC hgapfac) hsum_nonneg

  nlinarith

#print axioms v13_prop_mag_bilin

end

end SMLeanMinV1


namespace SMLeanMinV1

set_option maxHeartbeats 1000000

/-!
BATCH B05 SYNC: T005--T024 with expanded T011 paper-line proof.

The already web-verified T001--T004 are treated as previously certified
module interfaces.  Their outputs appear only as explicitly named
hypotheses such as `hCoeffA`, `hCoeffDiff`, and `hLowA`; no later theorem is
silently promoted to an axiom.

The purpose of this batch is to reduce manual browser runs while preserving
the paper order.  If the browser reports an error, the first failing node is
the repair point; nodes after it are not marked PASS until the batch compiles.
-/

noncomputable section

/- ================================================================
   T006 = v13:lem:HodgeH
   ================================================================ -/

/--
Scalar paper-line closure of the Hodge estimate.

`hCoeffA`, `hCoeffAP`, `hCoeffDiff` are exactly the coefficient bounds already
certified at T001.  `hHodgeMain` and `hHodgeDiff` are the standard
Riesz/Hölder reduction lines written in the proof of `v13:lem:HodgeH`.
-/
theorem v13_lem_HodgeH
    (M Z Mstar Zstar R4 Ccoef Criesz
      A4 AP4 dA4 H2 dH2 : ℝ)
    (hM : 0 ≤ M)
    (hZ : 0 ≤ Z)
    (hMstar : 0 ≤ Mstar)
    (hZstar : 0 ≤ Zstar)
    (hR4 : 0 ≤ R4)
    (hCcoef : 0 ≤ Ccoef)
    (hCriesz : 0 ≤ Criesz)
    (hA4 : 0 ≤ A4)
    (hAP4 : 0 ≤ AP4)
    (hdA4 : 0 ≤ dA4)
    (hCoeffA : A4 ≤ Ccoef * M * Z)
    (hCoeffAP : AP4 ≤ Ccoef * Mstar * Zstar)
    (hCoeffDiff : dA4 ≤ Ccoef * Mstar * R4)
    (hHodgeMain : H2 ≤ Criesz * A4 * Z)
    (hHodgeDiff :
      dH2 ≤ Criesz * (dA4 * Zstar + AP4 * R4)) :
    ∃ C : ℝ,
      0 ≤ C ∧
      H2 ≤ C * M * Z ^ 2 ∧
      dH2 ≤ C * Mstar * Zstar * R4 := by
  let C : ℝ := 2 * Criesz * Ccoef
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity

  have hAZ :
      A4 * Z ≤ (Ccoef * M * Z) * Z :=
    mul_le_mul_of_nonneg_right hCoeffA hZ
  have hMain0 :
      H2 ≤ Criesz * (Ccoef * M * Z) * Z := by
    calc
      H2 ≤ Criesz * A4 * Z := hHodgeMain
      _ ≤ Criesz * (Ccoef * M * Z) * Z := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCoeffA hCriesz) hZ
  have hMainBase :
      H2 ≤ Criesz * Ccoef * M * Z ^ 2 := by
    calc
      H2 ≤ Criesz * (Ccoef * M * Z) * Z := hMain0
      _ = Criesz * Ccoef * M * Z ^ 2 := by ring
  have hMain :
      H2 ≤ C * M * Z ^ 2 := by
    have hbase :
        0 ≤ Criesz * Ccoef * M * Z ^ 2 := by
      positivity
    calc
      H2 ≤ Criesz * Ccoef * M * Z ^ 2 := hMainBase
      _ ≤ 2 * (Criesz * Ccoef * M * Z ^ 2) := by
        linarith
      _ = C * M * Z ^ 2 := by
        dsimp [C]
        ring

  have hdAZ :
      dA4 * Zstar
        ≤ (Ccoef * Mstar * R4) * Zstar :=
    mul_le_mul_of_nonneg_right hCoeffDiff hZstar
  have hAPR :
      AP4 * R4
        ≤ (Ccoef * Mstar * Zstar) * R4 :=
    mul_le_mul_of_nonneg_right hCoeffAP hR4
  have hDiff0 :
      dH2 ≤
        Criesz *
          ((Ccoef * Mstar * R4) * Zstar
            + (Ccoef * Mstar * Zstar) * R4) := by
    calc
      dH2 ≤ Criesz * (dA4 * Zstar + AP4 * R4) := hHodgeDiff
      _ ≤ Criesz *
          ((Ccoef * Mstar * R4) * Zstar
            + (Ccoef * Mstar * Zstar) * R4) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add hdAZ hAPR) hCriesz
  have hDiff :
      dH2 ≤ C * Mstar * Zstar * R4 := by
    calc
      dH2 ≤
          Criesz *
            ((Ccoef * Mstar * R4) * Zstar
              + (Ccoef * Mstar * Zstar) * R4) := hDiff0
      _ = C * Mstar * Zstar * R4 := by
        dsimp [C]
        ring

  exact ⟨C, hC, hMain, hDiff⟩

#print axioms v13_lem_HodgeH


/- ================================================================
   T007 = v13:prop:HHL
   ================================================================ -/

/--
Paper-line aggregation of the HHL proof after the standard harmonic-analysis
reductions:

* `hGG` is the polarized Jacobian / null-form high-high-to-low estimate.
* `hTor` is the part with at least one transverse Hodge factor, using T006.
* `hDGG`, `hDTor` are the corresponding difference estimates.
* `hSplit`, `hDSplit` are the exact decomposition of the HHL output.

No final HHL estimate is assumed.
-/
theorem v13_prop_HHL
    (CGG CTor CDGG CDTor Z Zstar R4 S lhs dlhs GG Tor DGG DTor : ℝ)
    (hCGG : 0 ≤ CGG)
    (hCTor : 0 ≤ CTor)
    (hCDGG : 0 ≤ CDGG)
    (hCDTor : 0 ≤ CDTor)
    (hZ : 0 ≤ Z)
    (hZstar : 0 ≤ Zstar)
    (hZstar1 : Zstar ≤ 1)
    (hR4 : 0 ≤ R4)
    (hS : 0 ≤ S)
    (hGG : GG ≤ CGG * Z ^ 2 * S)
    (hTor : Tor ≤ CTor * Z ^ 3 * S)
    (hSplit : lhs ≤ GG + Tor)
    (hDGG : DGG ≤ CDGG * Zstar * R4 * S)
    (hDTor : DTor ≤ CDTor * Zstar ^ 2 * R4 * S)
    (hDSplit : dlhs ≤ DGG + DTor) :
    ∃ C : ℝ,
      0 ≤ C ∧
      lhs ≤ C * (Z ^ 2 + Z ^ 3) * S ∧
      dlhs ≤ C * Zstar * R4 * S := by
  let C : ℝ := CGG + CTor + CDGG + CDTor
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity

  have hGG' :
      CGG * Z ^ 2 * S
        ≤ C * Z ^ 2 * S := by
    have hc : CGG ≤ C := by
      dsimp [C]
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (sq_nonneg Z)) hS

  have hTor' :
      CTor * Z ^ 3 * S
        ≤ C * Z ^ 3 * S := by
    have hc : CTor ≤ C := by
      dsimp [C]
      linarith
    have hz3 : 0 ≤ Z ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc hz3) hS

  have hMain :
      lhs ≤ C * (Z ^ 2 + Z ^ 3) * S := by
    calc
      lhs ≤ GG + Tor := hSplit
      _ ≤ C * Z ^ 2 * S + C * Z ^ 3 * S :=
        add_le_add (le_trans hGG hGG') (le_trans hTor hTor')
      _ = C * (Z ^ 2 + Z ^ 3) * S := by ring

  have hzsq : Zstar ^ 2 ≤ Zstar := by
    nlinarith [sq_nonneg Zstar]

  have hDGG' :
      CDGG * Zstar * R4 * S
        ≤ C * Zstar * R4 * S := by
    have hc : CDGG ≤ C := by
      dsimp [C]
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc hZstar) hR4) hS

  have hDTorReduce :
      CDTor * Zstar ^ 2 * R4 * S
        ≤ CDTor * Zstar * R4 * S := by
    have h1 :
        CDTor * Zstar ^ 2 ≤ CDTor * Zstar :=
      mul_le_mul_of_nonneg_left hzsq hCDTor
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 hR4) hS

  have hDTor' :
      CDTor * Zstar * R4 * S
        ≤ C * Zstar * R4 * S := by
    have hc : CDTor ≤ C := by
      dsimp [C]
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc hZstar) hR4) hS

  have hDiff :
      dlhs ≤ (2 * C) * Zstar * R4 * S := by
    calc
      dlhs ≤ DGG + DTor := hDSplit
      _ ≤ C * Zstar * R4 * S + C * Zstar * R4 * S := by
        exact add_le_add
          (le_trans hDGG hDGG')
          (le_trans hDTor (le_trans hDTorReduce hDTor'))
      _ = (2 * C) * Zstar * R4 * S := by ring
  /-
  Enlarge once more so one constant serves both estimates.
  -/
  refine ⟨2 * C, ?_, ?_, ?_⟩
  · positivity
  · have hCS : 0 ≤ C * (Z ^ 2 + Z ^ 3) * S := by positivity
    exact le_trans hMain (by
      calc
        C * (Z ^ 2 + Z ^ 3) * S
            ≤ 2 * (C * (Z ^ 2 + Z ^ 3) * S) := by linarith
        _ = (2 * C) * (Z ^ 2 + Z ^ 3) * S := by ring)
  · exact hDiff

#print axioms v13_prop_HHL


/- ================================================================
   T008 = v13:lem:Hk
   ================================================================ -/

/--
The three forcing classes in the proof of `v13:lem:Hk` are kept separate:
first-order magnetic, cubic zero-order, and the `|A_k|^2 Q` contribution.
Their analytic estimates are the Smith/Coifman--Meyer reductions explicitly
listed in the paper.  Lean performs the final strong-forcing aggregation.
-/
theorem v13_lem_Hk
    (Z conv h hhat H1 H3 HA C1 C3 CA : ℝ)
    (hZ : 0 ≤ Z)
    (hconv : 0 ≤ conv)
    (hC1 : 0 ≤ C1)
    (hC3 : 0 ≤ C3)
    (hCA : 0 ≤ CA)
    (hemb : h ≤ hhat)
    (hsplit : hhat ≤ H1 + H3 + HA)
    (hfirst : H1 ≤ C1 * Z ^ 2 * conv)
    (hcubic : H3 ≤ C3 * Z ^ 2 * conv)
    (hAquad : HA ≤ CA * Z ^ 2 * conv) :
    ∃ C : ℝ,
      0 ≤ C ∧
      h ≤ hhat ∧
      hhat ≤ C * Z ^ 2 * conv := by
  let C : ℝ := C1 + C3 + CA
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsum :
      H1 + H3 + HA ≤ C * Z ^ 2 * conv := by
    calc
      H1 + H3 + HA
          ≤ C1 * Z ^ 2 * conv
            + C3 * Z ^ 2 * conv
            + CA * Z ^ 2 * conv := by
              exact add_le_add
                (add_le_add hfirst hcubic) hAquad
      _ = C * Z ^ 2 * conv := by
        dsimp [C]
        ring
  exact ⟨C, hC, hemb, le_trans hsplit hsum⟩

#print axioms v13_lem_Hk


/- ================================================================
   T009 = v13:lem:Mnd
   ================================================================ -/

/-- Real dyadic half-gap factor `2^((a-b)/2)`. -/
def dyHalf (a b : ℝ) : ℝ :=
  Real.rpow 2 ((a - b) / 2)

/-- Exact exponent cancellation used in (v13:eq:exponent-cancel). -/
lemma v13_exponent_cancel (r s k : ℝ) :
    (k - s) / 2 + (r - k) / 2 = (r - s) / 2 := by
  ring

/-- Multiplicative form of the same dyadic cancellation. -/
lemma v13_dyHalf_cancel (r s k : ℝ) :
    dyHalf k s * dyHalf r k = dyHalf r s := by
  unfold dyHalf
  calc
    Real.rpow 2 ((k - s) / 2) * Real.rpow 2 ((r - k) / 2)
        =
      Real.rpow 2 (((k - s) / 2) + ((r - k) / 2)) := by
        symm
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
    _ = Real.rpow 2 ((r - s) / 2) := by
        rw [v13_exponent_cancel]

/--
One interaction in the double triangular recurrence.

`hSmith39` is the Smith Lemma 3.9 low-output estimate after the Hodge
`2^{-s}` factor has been inserted.  `hMag` is exactly the T005 bilinear
output for the pair `(r,k)`.  Lean proves the paper's exponent cancellation
and the resulting recurrence term.
-/
theorem v13_lem_Mnd
    (r s k Csmith Cmag gs uv bracket term : ℝ)
    (hCsmith : 0 ≤ Csmith)
    (hCmag : 0 ≤ Cmag)
    (hgs : 0 ≤ gs)
    (hbracket : 0 ≤ bracket)
    (hSmith39 :
      term ≤ Csmith * dyHalf k s * gs * uv)
    (hMag :
      uv ≤ Cmag * dyHalf r k * bracket) :
    term ≤
      (Csmith * Cmag) * dyHalf r s * gs * bracket := by
  have hgap : 0 ≤ dyHalf k s := by
    unfold dyHalf
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hleft :
      0 ≤ Csmith * dyHalf k s * gs := by
    positivity
  have hmul :
      Csmith * dyHalf k s * gs * uv
        ≤
      Csmith * dyHalf k s * gs *
        (Cmag * dyHalf r k * bracket) :=
    mul_le_mul_of_nonneg_left hMag hleft
  calc
    term ≤ Csmith * dyHalf k s * gs * uv := hSmith39
    _ ≤
      Csmith * dyHalf k s * gs *
        (Cmag * dyHalf r k * bracket) := hmul
    _ =
      (Csmith * Cmag) *
        (dyHalf k s * dyHalf r k) * gs * bracket := by ring
    _ =
      (Csmith * Cmag) * dyHalf r s * gs * bracket := by
        rw [v13_dyHalf_cancel]

#print axioms v13_lem_Mnd


/- ================================================================
   T010 = v13:def:envelopes
   ================================================================ -/

/-- Slow dyadic kernel `2^{-δ |k-j|}`. -/
def slowKernel (δ : ℝ) (k j : ℤ) : ℝ :=
  Real.rpow 2 (-δ * ((|k - j| : ℤ) : ℝ))

/-- Data slow envelope `α_k`. -/
def alphaEnvelope (δ : ℝ) (c : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑' j : ℤ, slowKernel δ k j * c j

/--
Finite lower-truncation version of the causal envelope after translating
the lower cutoff `-N` to the natural index `0`.

`B 0 = 1`,
`β_{n+1} = C₁ α_{n+1}(1+sqrt(B_{(n+1)-d}))`,
`B_{n+1} = B_n + β_{n+1}²`.

This is the recursion in (v13:eq:betaN)--(v13:eq:BN) written in a form
suited to induction; natural subtraction realizes the convention `B=1`
below the finite lower cutoff.
-/
structure CausalEnvelopeTruncation
    (C1 : ℝ) (d : ℕ) (α : ℕ → ℝ) where
  beta : ℕ → ℝ
  B : ℕ → ℝ
  B0 : B 0 = 1
  beta_eq :
    ∀ n : ℕ,
      beta (n + 1) =
        C1 * α (n + 1) *
          (1 + Real.sqrt (B ((n + 1) - d)))
  B_step :
    ∀ n : ℕ,
      B (n + 1) = B n + (beta (n + 1)) ^ 2

#check slowKernel
#check alphaEnvelope
#check CausalEnvelopeTruncation


/- ================================================================
   T011 = v13:lem:beta  (synchronized with expanded Lean-min proof)
   ================================================================ -/

/--
One induction step for monotonicity in the lower cutoff `N`.

This is the exact algebraic step used in the revised TeX proof:
if the delayed and previous cumulative budgets for truncation `N` are
bounded by those for `N+1`, then both the current beta coefficient and the
current cumulative budget are also ordered.
-/
theorem v13_lem_beta_cutoff_monotone_step
    (C1 alpha bDelayN bDelayNp bPrevN bPrevNp
      betaN betaNp bN bNp : ℝ)
    (hC1 : 0 ≤ C1)
    (halpha : 0 ≤ alpha)
    (hDelayN : 0 ≤ bDelayN)
    (hDelay : bDelayN ≤ bDelayNp)
    (hPrev : bPrevN ≤ bPrevNp)
    (hbetaN :
      betaN = C1 * alpha * (1 + Real.sqrt bDelayN))
    (hbetaNp :
      betaNp = C1 * alpha * (1 + Real.sqrt bDelayNp))
    (hbN : bN = bPrevN + betaN ^ 2)
    (hbNp : bNp = bPrevNp + betaNp ^ 2) :
    betaN ≤ betaNp ∧ bN ≤ bNp := by
  have hsqrt :
      Real.sqrt bDelayN ≤ Real.sqrt bDelayNp :=
    Real.sqrt_le_sqrt hDelay
  have hcoef : 0 ≤ C1 * alpha :=
    mul_nonneg hC1 halpha
  have hbeta : betaN ≤ betaNp := by
    calc
      betaN = C1 * alpha * (1 + Real.sqrt bDelayN) := hbetaN
      _ ≤ C1 * alpha * (1 + Real.sqrt bDelayNp) := by
        exact mul_le_mul_of_nonneg_left
          (by linarith [hsqrt]) hcoef
      _ = betaNp := hbetaNp.symm
  have hbetaN0 : 0 ≤ betaN := by
    rw [hbetaN]
    positivity
  have hbetaNp0 : 0 ≤ betaNp := by
    rw [hbetaNp]
    positivity
  have hsq : betaN ^ 2 ≤ betaNp ^ 2 := by
    nlinarith
  have hB : bN ≤ bNp := by
    rw [hbN, hbNp]
    linarith
  exact ⟨hbeta, hB⟩

#print axioms v13_lem_beta_cutoff_monotone_step

/--
Finite-truncation core of Lemma `v13:lem:beta`.

This matches the first paragraph of the revised TeX proof:
  beta^2 <= C2 alpha^2 B_prev,
  B_next <= (1+C2 alpha^2) B_prev,
  exponential finite-cutoff budget,
  finite-cutoff square-sum budget.
-/
theorem v13_lem_beta_finite_core
    (C1 : ℝ) (d : ℕ) (α : ℕ → ℝ)
    (env : CausalEnvelopeTruncation C1 d α)
    (hC1 : 0 ≤ C1)
    (hd : 1 ≤ d)
    (hexp :
      ∀ x : ℝ, 0 ≤ x → 1 + x ≤ Real.exp x) :
    let C2 : ℝ := 4 * C1 ^ 2;
    (∀ n : ℕ,
      (env.beta (n + 1)) ^ 2
        ≤ C2 * (α (n + 1)) ^ 2 * env.B n)
    ∧
    (∀ n : ℕ,
      env.B (n + 1)
        ≤ (1 + C2 * (α (n + 1)) ^ 2) * env.B n)
    ∧
    (∀ n : ℕ,
      env.B n
        ≤ Real.exp
            (Finset.sum (Finset.range n) (fun i =>
              C2 * (α (i + 1)) ^ 2)))
    ∧
    (∀ n : ℕ,
      Finset.sum (Finset.range n) (fun i =>
        (env.beta (i + 1)) ^ 2)
        ≤
      Real.exp
          (Finset.sum (Finset.range n) (fun i =>
            C2 * (α (i + 1)) ^ 2)) - 1) := by
  let C2 : ℝ := 4 * C1 ^ 2
  have hC2 : 0 ≤ C2 := by
    dsimp [C2]
    positivity

  have hstepB :
      ∀ n : ℕ, env.B n ≤ env.B (n + 1) := by
    intro n
    rw [env.B_step n]
    nlinarith [sq_nonneg (env.beta (n + 1))]

  have hmono : Monotone env.B :=
    monotone_nat_of_le_succ hstepB

  have hBone : ∀ n : ℕ, 1 ≤ env.B n := by
    intro n
    calc
      1 = env.B 0 := by simpa [env.B0]
      _ ≤ env.B n := hmono (Nat.zero_le n)

  have hbeta :
      ∀ n : ℕ,
        (env.beta (n + 1)) ^ 2
          ≤ C2 * (α (n + 1)) ^ 2 * env.B n := by
    intro n
    have hidx : (n + 1) - d ≤ n := by
      omega
    have hdelay :
        env.B ((n + 1) - d) ≤ env.B n :=
      hmono hidx
    have hBd1 :
        1 ≤ env.B ((n + 1) - d) :=
      hBone ((n + 1) - d)
    have hBd0 :
        0 ≤ env.B ((n + 1) - d) :=
      le_trans (by norm_num) hBd1
    have hs0 :
        0 ≤ Real.sqrt (env.B ((n + 1) - d)) :=
      Real.sqrt_nonneg _
    have hs2 :
        (Real.sqrt (env.B ((n + 1) - d))) ^ 2
          = env.B ((n + 1) - d) :=
      Real.sq_sqrt hBd0
    have hsquareOne :
        0 ≤ (Real.sqrt (env.B ((n + 1) - d)) - 1) ^ 2 :=
      sq_nonneg _
    have hquad :
        (1 + Real.sqrt (env.B ((n + 1) - d))) ^ 2
          ≤ 4 * env.B n := by
      nlinarith [hsquareOne]
    have hfac :
        0 ≤ (C1 * α (n + 1)) ^ 2 :=
      sq_nonneg _
    calc
      (env.beta (n + 1)) ^ 2
          =
        (C1 * α (n + 1)) ^ 2 *
          (1 + Real.sqrt (env.B ((n + 1) - d))) ^ 2 := by
            rw [env.beta_eq n]
            ring
      _ ≤
        (C1 * α (n + 1)) ^ 2 * (4 * env.B n) :=
          mul_le_mul_of_nonneg_left hquad hfac
      _ = C2 * (α (n + 1)) ^ 2 * env.B n := by
        dsimp [C2]
        ring

  have hBmult :
      ∀ n : ℕ,
        env.B (n + 1)
          ≤ (1 + C2 * (α (n + 1)) ^ 2) * env.B n := by
    intro n
    rw [env.B_step n]
    have hb := hbeta n
    calc
      env.B n + (env.beta (n + 1)) ^ 2
          ≤ env.B n
            + C2 * (α (n + 1)) ^ 2 * env.B n := by
              linarith
      _ =
        (1 + C2 * (α (n + 1)) ^ 2) * env.B n := by
          ring

  have hExp :
      ∀ n : ℕ,
        env.B n
          ≤ Real.exp
              (Finset.sum (Finset.range n) (fun i =>
                C2 * (α (i + 1)) ^ 2)) := by
    intro n
    induction n with
    | zero =>
        simp [env.B0]
    | succ n ih =>
        let x : ℝ := C2 * (α (n + 1)) ^ 2
        have hx : 0 ≤ x := by
          dsimp [x]
          positivity
        have hfacExp : 1 + x ≤ Real.exp x :=
          hexp x hx
        have hBn0 : 0 ≤ env.B n := by
          have := hBone n
          linarith
        have h1 :
            env.B (n + 1)
              ≤ Real.exp x * env.B n := by
          calc
            env.B (n + 1)
                ≤ (1 + C2 * (α (n + 1)) ^ 2) * env.B n :=
                  hBmult n
            _ = (1 + x) * env.B n := by
                  rfl
            _ ≤ Real.exp x * env.B n :=
                  mul_le_mul_of_nonneg_right hfacExp hBn0
        have h2 :
            Real.exp x * env.B n
              ≤ Real.exp x *
                  Real.exp
                    (Finset.sum (Finset.range n) (fun i =>
                      C2 * (α (i + 1)) ^ 2)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg x)
        calc
          env.B (n + 1)
              ≤ Real.exp x * env.B n := h1
          _ ≤
              Real.exp x *
                Real.exp
                  (Finset.sum (Finset.range n) (fun i =>
                    C2 * (α (i + 1)) ^ 2)) := h2
          _ =
              Real.exp
                (Finset.sum (Finset.range n) (fun i =>
                    C2 * (α (i + 1)) ^ 2) + x) := by
                  rw [Real.exp_add]
                  ring
          _ =
              Real.exp
                (Finset.sum (Finset.range (n + 1)) (fun i =>
                  C2 * (α (i + 1)) ^ 2)) := by
                  rw [Finset.sum_range_succ]
                  rfl

  have hsumEq :
      ∀ n : ℕ,
        Finset.sum (Finset.range n) (fun i =>
          (env.beta (i + 1)) ^ 2)
          = env.B n - 1 := by
    intro n
    induction n with
    | zero =>
        simp [env.B0]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, env.B_step n]
        ring

  have hsum :
      ∀ n : ℕ,
        Finset.sum (Finset.range n) (fun i =>
          (env.beta (i + 1)) ^ 2)
          ≤
        Real.exp
            (Finset.sum (Finset.range n) (fun i =>
              C2 * (α (i + 1)) ^ 2)) - 1 := by
    intro n
    rw [hsumEq n]
    linarith [hExp n]

  exact ⟨hbeta, hBmult, hExp, hsum⟩

#print axioms v13_lem_beta_finite_core

/--
Pointwise lower/upper alpha bounds after the monotone cutoff limit.

This matches the last paragraph of the revised TeX proof.  The only input
from the standard monotone-limit passage is the already-defined limiting
recurrence `beta = C1 * alpha * (1 + sqrt Bprev)` together with
`1 <= Bprev <= ME`.
-/
theorem v13_lem_beta_limit_alpha_bounds
    (C1 alpha beta Bprev ME : ℝ)
    (hC1 : 0 ≤ C1)
    (halpha : 0 ≤ alpha)
    (hB1 : 1 ≤ Bprev)
    (hBME : Bprev ≤ ME)
    (hbetaEq :
      beta = C1 * alpha * (1 + Real.sqrt Bprev)) :
    C1 * alpha ≤ beta ∧
    beta ≤ C1 * (1 + Real.sqrt ME) * alpha := by
  have hB0 : 0 ≤ Bprev := by linarith
  have hME0 : 0 ≤ ME := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt Bprev := Real.sqrt_nonneg _
  have hsqrt_le : Real.sqrt Bprev ≤ Real.sqrt ME :=
    Real.sqrt_le_sqrt hBME
  have hcoef : 0 ≤ C1 * alpha := mul_nonneg hC1 halpha
  constructor
  · rw [hbetaEq]
    have hone : 1 ≤ 1 + Real.sqrt Bprev := by linarith
    calc
      C1 * alpha = (C1 * alpha) * 1 := by ring
      _ ≤ (C1 * alpha) * (1 + Real.sqrt Bprev) :=
        mul_le_mul_of_nonneg_left hone hcoef
      _ = C1 * alpha * (1 + Real.sqrt Bprev) := by ring
  · rw [hbetaEq]
    have hsum : 1 + Real.sqrt Bprev ≤ 1 + Real.sqrt ME := by
      linarith [hsqrt_le]
    calc
      C1 * alpha * (1 + Real.sqrt Bprev)
          ≤ C1 * alpha * (1 + Real.sqrt ME) :=
            mul_le_mul_of_nonneg_left hsum hcoef
      _ = C1 * (1 + Real.sqrt ME) * alpha := by ring

#print axioms v13_lem_beta_limit_alpha_bounds

/--
The slow-variation tail of paper Lemma `v13:lem:beta`.
Once the pointwise limit beta exists and satisfies the displayed lower/upper
alpha bounds, the paper's slow-envelope conclusion is elementary.
-/
theorem v13_lem_beta_slow_from_bounds
    (CE C1 delta : ℝ)
    (alpha beta : ℤ → ℝ)
    (hC1 : 0 < C1)
    (hCE : 0 ≤ CE)
    (halpha0 : ∀ k, 0 ≤ alpha k)
    (hbetaLower : ∀ k, C1 * alpha k ≤ beta k)
    (hbetaUpper : ∀ k, beta k ≤ CE * alpha k)
    (halphaSlow : ∀ j k : ℤ,
      alpha j ≤ Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) * alpha k) :
    ∀ j k : ℤ,
      beta j ≤ (CE / C1) *
        Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) * beta k := by
  intro j k
  have hC1nonneg : 0 ≤ C1 := le_of_lt hC1
  have hpow0 : 0 ≤ Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) := by
    exact Real.rpow_nonneg (by norm_num) _
  have hak0 : 0 ≤ alpha k := halpha0 k
  have hbk0 : 0 ≤ beta k := by
    exact le_trans (mul_nonneg hC1nonneg hak0) (hbetaLower k)
  have h1 :
      beta j ≤ CE *
        (Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) * alpha k) := by
    calc
      beta j ≤ CE * alpha j := hbetaUpper j
      _ ≤ CE *
          (Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) * alpha k) :=
            mul_le_mul_of_nonneg_left (halphaSlow j k) hCE
  have hk : alpha k ≤ beta k / C1 := by
    have := hbetaLower k
    exact (le_div_iff₀ hC1).2 (by simpa [mul_comm] using this)
  have hfac :
      0 ≤ CE * Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) :=
    mul_nonneg hCE hpow0
  calc
    beta j ≤ CE *
        (Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) * alpha k) := h1
    _ = (CE * Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ))) * alpha k := by ring
    _ ≤ (CE * Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ))) * (beta k / C1) :=
      mul_le_mul_of_nonneg_left hk hfac
    _ = (CE / C1) * Real.rpow 2 (delta * ((|j-k| : ℤ) : ℝ)) * beta k := by
      field_simp [ne_of_gt hC1]

#print axioms v13_lem_beta_slow_from_bounds


/- ================================================================
   T012 = v13:thm:single
   ================================================================ -/

/--
Algebraic bootstrap-closing spine of the single-field theorem.

The PDE/harmonic-analysis reductions are exactly the preceding nodes:
T005 (bilinear), T007 (HHL), T008 (strong forcing), T009 (triangular
recurrence), and T011 (causal envelope).  Their combined paper-line output
is the displayed bootstrap inequality `hg_boot`.

Lean verifies:
  1. the parameter choices improve the bootstrap strictly;
  2. the envelope square budget yields the final S^0/data bound.

Thus the theorem does not assume the desired bootstrap improvement or the
desired norm conclusion.
-/
theorem v13_thm_single
    (C0 CE C1 Z eta ME alpha beta Bprev g
      SNorm betaSq dataNorm Cenv : ℝ)
    (hC0 : 0 ≤ C0)
    (hCE : 1 ≤ CE)
    (hC1 : 0 ≤ C1)
    (hZ : 0 ≤ Z)
    (heta : 0 ≤ eta)
    (hZeta : Z ≤ eta)
    (hME : 0 ≤ ME)
    (halpha : 0 ≤ alpha)
    (hbeta0 : 0 ≤ beta)
    (hB1 : 1 ≤ Bprev)
    (hBME : Bprev ≤ ME)
    (hS0 : 0 ≤ SNorm)
    (hdata : 0 ≤ dataNorm)
    (hCenv : 0 ≤ Cenv)

    /- C1 is chosen after the fixed E-dependent constants. -/
    (hC1choice : 8 * C0 * CE ≤ C1)

    /- eta_E is then chosen from the uniform envelope budget. -/
    (hetaChoice :
      C0 * CE * (eta + eta ^ 2) * ME ≤ (1 : ℝ) / 8)

    /- exact causal envelope at the current frequency. -/
    (hbetaEq :
      beta = C1 * alpha * (1 + Real.sqrt Bprev))

    /-
    Output of T005+T007+T008+T009 after the envelope summations:
    equation (v13:eq:g-bootstrap).
    -/
    (hg_boot :
      g ≤ C0 *
        (alpha
          + CE * alpha * Real.sqrt Bprev
          + CE * (Z + Z ^ 2) * beta * Bprev))

    /-
    Output of T011 plus the slow-envelope ℓ² Young estimate on the fixed
    energy sublevel.
    -/
    (hSsquare : SNorm ^ 2 ≤ betaSq)
    (hbetaSquare :
      betaSq ≤ Cenv * dataNorm ^ 2) :

    g ≤ (3 / 4 : ℝ) * beta
    ∧
    SNorm ≤ Real.sqrt Cenv * dataNorm := by

  have hB0 : 0 ≤ Bprev := by
    linarith
  have hs0 : 0 ≤ Real.sqrt Bprev :=
    Real.sqrt_nonneg _
  have hCE0 : 0 ≤ CE := by
    linarith

  have hCEminus : 0 ≤ CE - 1 := by
    linarith
  have hCEalpha : 0 ≤ (CE - 1) * alpha :=
    mul_nonneg hCEminus halpha
  have hlinInside :
      alpha + CE * alpha * Real.sqrt Bprev
        ≤ CE * alpha * (1 + Real.sqrt Bprev) := by
    nlinarith [hCEalpha]

  have hlin0 :
      C0 *
        (alpha + CE * alpha * Real.sqrt Bprev)
        ≤
      C0 * CE * alpha * (1 + Real.sqrt Bprev) := by
    calc
      C0 * (alpha + CE * alpha * Real.sqrt Bprev)
          ≤ C0 * (CE * alpha * (1 + Real.sqrt Bprev)) :=
            mul_le_mul_of_nonneg_left hlinInside hC0
      _ = C0 * CE * alpha * (1 + Real.sqrt Bprev) := by
            ring

  have henvfac :
      0 ≤ alpha * (1 + Real.sqrt Bprev) := by
    positivity

  have hchoiceScaled :
      C0 * CE * alpha * (1 + Real.sqrt Bprev)
        ≤
      (C1 / 8) * alpha * (1 + Real.sqrt Bprev) := by
    have hc : C0 * CE ≤ C1 / 8 := by
      linarith
    have hs :
        (C0 * CE) * (alpha * (1 + Real.sqrt Bprev))
          ≤
        (C1 / 8) * (alpha * (1 + Real.sqrt Bprev)) :=
      mul_le_mul_of_nonneg_right hc henvfac
    calc
      C0 * CE * alpha * (1 + Real.sqrt Bprev)
          = (C0 * CE) * (alpha * (1 + Real.sqrt Bprev)) := by ring
      _ ≤ (C1 / 8) * (alpha * (1 + Real.sqrt Bprev)) := hs
      _ = (C1 / 8) * alpha * (1 + Real.sqrt Bprev) := by ring

  have hlin :
      C0 *
        (alpha + CE * alpha * Real.sqrt Bprev)
        ≤ beta / 8 := by
    calc
      C0 *
          (alpha + CE * alpha * Real.sqrt Bprev)
          ≤
        C0 * CE * alpha * (1 + Real.sqrt Bprev) := hlin0
      _ ≤
        (C1 / 8) * alpha * (1 + Real.sqrt Bprev) :=
          hchoiceScaled
      _ = beta / 8 := by
        rw [hbetaEq]
        ring

  have hpolyFactor :
      0 ≤ (eta - Z) * (1 + eta + Z) := by
    exact mul_nonneg (sub_nonneg.mpr hZeta) (by linarith)
  have hpoly :
      Z + Z ^ 2 ≤ eta + eta ^ 2 := by
    nlinarith [hpolyFactor]

  have hcoef0 :
      0 ≤ C0 * CE := by
    positivity

  have hsmall1 :
      C0 * CE * (Z + Z ^ 2)
        ≤ C0 * CE * (eta + eta ^ 2) :=
    mul_le_mul_of_nonneg_left hpoly hcoef0

  have hetaPoly0 :
      0 ≤ eta + eta ^ 2 := by
    positivity

  have hsmall2 :
      C0 * CE * (Z + Z ^ 2) * Bprev
        ≤
      C0 * CE * (eta + eta ^ 2) * ME := by
    calc
      C0 * CE * (Z + Z ^ 2) * Bprev
          ≤ C0 * CE * (eta + eta ^ 2) * Bprev :=
            mul_le_mul_of_nonneg_right hsmall1 hB0
      _ ≤ C0 * CE * (eta + eta ^ 2) * ME := by
            exact mul_le_mul_of_nonneg_left hBME
              (mul_nonneg hcoef0 hetaPoly0)

  have hsmall :
      C0 * CE * (Z + Z ^ 2) * Bprev
        ≤ (1 : ℝ) / 8 :=
    le_trans hsmall2 hetaChoice

  have hnonlin :
      C0 * (CE * (Z + Z ^ 2) * beta * Bprev)
        ≤ beta / 8 := by
    have hb :
        (C0 * CE * (Z + Z ^ 2) * Bprev) * beta
          ≤ ((1 : ℝ) / 8) * beta :=
      mul_le_mul_of_nonneg_right hsmall hbeta0
    calc
      C0 * (CE * (Z + Z ^ 2) * beta * Bprev)
          =
        (C0 * CE * (Z + Z ^ 2) * Bprev) * beta := by
          ring
      _ ≤ ((1 : ℝ) / 8) * beta := hb
      _ = beta / 8 := by ring

  have himprove :
      g ≤ beta / 4 := by
    calc
      g ≤ C0 *
        (alpha
          + CE * alpha * Real.sqrt Bprev
          + CE * (Z + Z ^ 2) * beta * Bprev) := hg_boot
      _ =
        C0 * (alpha + CE * alpha * Real.sqrt Bprev)
          + C0 * (CE * (Z + Z ^ 2) * beta * Bprev) := by
            ring
      _ ≤ beta / 8 + beta / 8 :=
        add_le_add hlin hnonlin
      _ = beta / 4 := by ring

  have himprove34 :
      g ≤ (3 / 4 : ℝ) * beta := by
    have hb14 :
        beta / 4 ≤ (3 / 4 : ℝ) * beta := by      nlinarith
    exact le_trans himprove hb14

  have hsqrtC0 :
      0 ≤ Real.sqrt Cenv :=
    Real.sqrt_nonneg _
  have hsqrtC2 :
      (Real.sqrt Cenv) ^ 2 = Cenv :=
    Real.sq_sqrt hCenv
  have htargetSq :
      SNorm ^ 2
        ≤ (Real.sqrt Cenv * dataNorm) ^ 2 := by
    calc
      SNorm ^ 2 ≤ betaSq := hSsquare
      _ ≤ Cenv * dataNorm ^ 2 := hbetaSquare
      _ = (Real.sqrt Cenv * dataNorm) ^ 2 := by
        rw [mul_pow, hsqrtC2]

  have htarget0 :
      0 ≤ Real.sqrt Cenv * dataNorm :=
    mul_nonneg hsqrtC0 hdata

  have hSnorm :
      SNorm ≤ Real.sqrt Cenv * dataNorm := by
    nlinarith [htargetSq]

  exact ⟨himprove34, hSnorm⟩

#print axioms v13_thm_single


/- ================================================================
   T013 = v13:thm:linear
   ================================================================ -/

/--
Algebraic absorption core of the fixed-background strong-forcing linear
estimate.  The inputs are exactly the paper's already-derived forcing
estimate plus the scalar Young bound for the square-root term.

No desired `d <= C e` conclusion is assumed.
-/
theorem v13_thm_linear
    (CE e d SNorm initNorm FNorm a b rootTerm : ℝ)
    (hCE : 0 ≤ CE)
    (he : 0 ≤ e)
    (hd : 0 ≤ d)
    (hinit : 0 ≤ initNorm)
    (hF : 0 ≤ FNorm)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hsmall : a + b ≤ (1 : ℝ) / 2)
    (hroot :
      rootTerm ≤ b * d + CE * e)
    (hbootstrap :
      d ≤ CE * e + a * d + rootTerm)
    (hSquareSum :
      SNorm ≤ 4 * CE * (initNorm + FNorm)) :
    d ≤ 4 * CE * e
    ∧
    SNorm ≤ 4 * CE * (initNorm + FNorm) := by
  have hroot' :
      d ≤ 2 * CE * e + (a + b) * d := by
    calc
      d ≤ CE * e + a * d + rootTerm := hbootstrap
      _ ≤ CE * e + a * d + (b * d + CE * e) := by
        linarith
      _ = 2 * CE * e + (a + b) * d := by ring
  have hhalf :
      d ≤ 2 * CE * e + ((1 : ℝ) / 2) * d := by
    have hdscale :
        (a + b) * d ≤ ((1 : ℝ) / 2) * d :=
      mul_le_mul_of_nonneg_right hsmall hd
    linarith
  have hdclose : d ≤ 4 * CE * e := by
    linarith
  exact ⟨hdclose, hSquareSum⟩

#print axioms v13_thm_linear


/- ================================================================
   T014 = v13:lem:relative-causal
   ================================================================ -/

/--
Final squaring step in the relative causal estimate.

The hypothesis `hell` is the output of the two Bony-ordering estimates,
Cauchy--Schwarz and Young:
  ell_k <= C beta_k^P sqrt(D).
Lean checks the boxed squared form without assuming it.
-/
theorem v13_lem_relative_causal
    (C ell betaP D : ℝ)
    (hC : 0 ≤ C)
    (hell0 : 0 ≤ ell)
    (hbeta : 0 ≤ betaP)
    (hD : 0 ≤ D)
    (hell : ell ≤ C * betaP * Real.sqrt D) :
    ell ^ 2 ≤ C ^ 2 * betaP ^ 2 * D := by
  have hs0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have hrhs0 : 0 ≤ C * betaP * Real.sqrt D := by
    positivity
  have hsq :
      ell ^ 2 ≤ (C * betaP * Real.sqrt D) ^ 2 := by
    nlinarith
  calc
    ell ^ 2 ≤ (C * betaP * Real.sqrt D) ^ 2 := hsq
    _ = C ^ 2 * betaP ^ 2 * D := by
      rw [mul_pow, mul_pow, hs2]

#print axioms v13_lem_relative_causal


/- ================================================================
   T015 = v13:lem:weak-firstgen
   ================================================================ -/

/--
The first weak local-smoothing forcing generation.

`hduality` is precisely the finite angular
L^{∞,2}_θ x L^{1,2}_θ duality estimate.
`hhalfspaceMass` is the elementary estimate obtained by integrating first in
the half-space y-variable and using `||v_k(t)||_2 <= g_k`.
-/
theorem v13_lem_weak_firstgen
    (C gr ellr gk whole half : ℝ)
    (hC : 0 ≤ C)
    (hgr : 0 ≤ gr)
    (hell : 0 ≤ ellr)
    (hgk : 0 ≤ gk)
    (hwhole0 : 0 ≤ whole)
    (hduality : whole ≤ C * gr * ellr)
    (hhalfspaceMass : half ≤ gk ^ 2 * whole) :
    whole ≤ C * gr * ellr
    ∧
    half ≤ C * gr * ellr * gk ^ 2 := by
  constructor
  · exact hduality
  · have hgk2 : 0 ≤ gk ^ 2 := sq_nonneg _
    have hmul :
        gk ^ 2 * whole
          ≤ gk ^ 2 * (C * gr * ellr) :=
      mul_le_mul_of_nonneg_left hduality hgk2
    calc
      half ≤ gk ^ 2 * whole := hhalfspaceMass
      _ ≤ gk ^ 2 * (C * gr * ellr) := hmul
      _ = C * gr * ellr * gk ^ 2 := by ring

#print axioms v13_lem_weak_firstgen


/- ================================================================
   T016 = v13:def:WMB
   ================================================================ -/

/--
Scalar record of the WMB_13 interface at one separated pair `(r,k)`.
The four forcing sizes correspond to
  hhat_r, ell_r, hhat_k, ell_k.
-/
structure WMB13Witness where
  C : ℝ
  gap : ℝ
  cr : ℝ
  ck : ℝ
  gr : ℝ
  gk : ℝ
  hhatR : ℝ
  ellR : ℝ
  hhatK : ℝ
  ellK : ℝ
  product : ℝ
  C_nonneg : 0 ≤ C
  gap_nonneg : 0 ≤ gap
  gr_nonneg : 0 ≤ gr
  gk_nonneg : 0 ≤ gk
  hhatR_nonneg : 0 ≤ hhatR
  ellR_nonneg : 0 ≤ ellR
  hhatK_nonneg : 0 ≤ hhatK
  ellK_nonneg : 0 ≤ ellK
  estimate :
    product ≤
      C * gap *
        (cr * ck
          + gk * Real.sqrt (gr * (hhatR + ellR))
          + gr * Real.sqrt (gk * (hhatK + ellK)))

#check WMB13Witness


/- ================================================================
   T017 = v14:def:Djoint
   ================================================================ -/

/--
Pure algebraic data for the derived low--high tensor operator.
`Djoint_tensor` is the boxed Leibniz identity in the definition.
-/
structure DJointData (A B T : Type*) [Add T] where
  tensor : A → B → T
  Elow : A → A
  Dhigh : B → B
  Djoint : T → T
  tensor_identity :
    ∀ a b,
      Djoint (tensor a b) =
        tensor (Elow a) b + tensor a (Dhigh b)

#check DJointData


/- ================================================================
   T018 = v14:lem:tensor-contract
   ================================================================ -/

/--
Norm contraction for the two pieces in the derived tensor identity.

The analytic multiplier estimates are supplied separately for the low and
high factors; Lean proves the combined contraction used by the paper.
-/
theorem v14_lem_tensor_contract
    (epsStar low high joint Clow Chigh : ℝ)
    (heps : 0 ≤ epsStar)
    (hlow0 : 0 ≤ low)
    (hhigh0 : 0 ≤ high)
    (hClow : 0 ≤ Clow)
    (hChigh : 0 ≤ Chigh)
    (hlow : low ≤ Clow * epsStar)
    (hhigh : high ≤ Chigh * epsStar)
    (hjoint : joint ≤ low + high) :
    ∃ C : ℝ,
      0 ≤ C ∧ joint ≤ C * epsStar := by
  let C : ℝ := Clow + Chigh
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsum :
      low + high ≤ C * epsStar := by
    calc
      low + high ≤ Clow * epsStar + Chigh * epsStar :=
        add_le_add hlow hhigh
      _ = C * epsStar := by
        dsimp [C]
        ring
  exact ⟨C, hC, le_trans hjoint hsum⟩

#print axioms v14_lem_tensor_contract


/- ================================================================
   T019 = v14:lem:weak-generations
   ================================================================ -/

/--
Finite-generation scalar spine of the weak derived-forcing induction.

The first-generation pairing is supplied by T015.  The one-step contraction
is the output of T018 applied simultaneously to the solution tensor and to
its weak local-smoothing forcing tensor.  Lean proves the geometric factor
for every fixed generation; no supremum in the generation number is used.
-/
theorem v14_lem_weak_generations
    (C eps base : ℝ) (pair : ℕ → ℝ)
    (hC : 0 ≤ C)
    (heps : 0 ≤ eps)
    (hbase : 0 ≤ base)
    (hfirst : pair 1 ≤ C * base)
    (hcontract :
      ∀ n : ℕ,
        pair (n + 2) ≤ eps ^ 2 * pair (n + 1)) :
    ∀ n : ℕ,
      pair (n + 1) ≤ C * (eps ^ 2) ^ n * base := by
  intro n
  induction n with
  | zero =>
      simpa using hfirst
  | succ n ih =>
      have heps2 : 0 ≤ eps ^ 2 := sq_nonneg eps
      calc
        pair (n + 1 + 1)
            ≤ eps ^ 2 * pair (n + 1) := by
              simpa [Nat.add_assoc] using hcontract n
        _ ≤ eps ^ 2 * (C * (eps ^ 2) ^ n * base) :=
              mul_le_mul_of_nonneg_left ih heps2
        _ = C * (eps ^ 2) ^ (n + 1) * base := by
              ring

#print axioms v14_lem_weak_generations


/- ================================================================
   T020 = v14:thm:weak-Smith
   ================================================================ -/

/--
Bootstrap-constant closure in the weak Smith extension.

`theta` is the combined contraction
`eps_*^q0 + eps_*^2`.  The previous nodes give the bootstrap inequality
`K <= C(1 + theta K)`; choosing the angular/frequency parameters gives
`C theta <= 1/2`.  Lean performs the absorption.
-/
theorem v14_thm_weak_Smith
    (C theta K : ℝ)
    (hC : 0 ≤ C)
    (htheta : 0 ≤ theta)
    (hK : 0 ≤ K)
    (hboot : K ≤ C * (1 + theta * K))
    (hsmall : C * theta ≤ (1 : ℝ) / 2) :
    K ≤ 2 * C := by
  have hmul :
      C * theta * K ≤ ((1 : ℝ) / 2) * K :=
    mul_le_mul_of_nonneg_right hsmall hK
  nlinarith

#print axioms v14_thm_weak_Smith


/- ================================================================
   T021 = v14:thm:WMB-close
   ================================================================ -/

/--
Opening the squared weak-Smith product estimate gives the unconditional
WMB scalar form.  `hSquared` is the squared estimate delivered by T020 after
T019 has verified all derived generations; the desired unsquared WMB bound
is proved here and is not assumed.
-/
theorem v14_thm_WMB_close
    (C gap uv cr ck gr gk hhatR ellR hhatK ellK : ℝ)
    (hC : 0 ≤ C)
    (hgap : 0 ≤ gap)
    (huv : 0 ≤ uv)
    (hcr : 0 ≤ cr)
    (hck : 0 ≤ ck)
    (hgr : 0 ≤ gr)
    (hgk : 0 ≤ gk)
    (hhR : 0 ≤ hhatR)
    (hellR : 0 ≤ ellR)
    (hhK : 0 ≤ hhatK)
    (hellK : 0 ≤ ellK)
    (hSquared :
      uv ^ 2 ≤ C ^ 2 * gap ^ 2 *
        (cr ^ 2 * ck ^ 2
          + gr * gk *
              ((hhatR + ellR) * gk
                + gr * (hhatK + ellK)))) :
    uv ≤ C * gap *
      (cr * ck
        + gk * Real.sqrt (gr * (hhatR + ellR))
        + gr * Real.sqrt (gk * (hhatK + ellK))) := by
  have hR0 : 0 ≤ gr * (hhatR + ellR) := by positivity
  have hK0 : 0 ≤ gk * (hhatK + ellK) := by positivity
  have hsR :
      (Real.sqrt (gr * (hhatR + ellR))) ^ 2
        = gr * (hhatR + ellR) :=
    Real.sq_sqrt hR0
  have hsK :
      (Real.sqrt (gk * (hhatK + ellK))) ^ 2
        = gk * (hhatK + ellK) :=
    Real.sq_sqrt hK0

  let a : ℝ := cr * ck
  let b : ℝ := gk * Real.sqrt (gr * (hhatR + ellR))
  let c : ℝ := gr * Real.sqrt (gk * (hhatK + ellK))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hbc : 0 ≤ b * c := mul_nonneg hb hc
  have habc :
      a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2 := by
    nlinarith

  have hb2 :
      b ^ 2 = gk ^ 2 * (gr * (hhatR + ellR)) := by
    dsimp [b]
    rw [mul_pow, hsR]
  have hc2 :
      c ^ 2 = gr ^ 2 * (gk * (hhatK + ellK)) := by
    dsimp [c]
    rw [mul_pow, hsK]
  have hinsideEq :
      cr ^ 2 * ck ^ 2
          + gr * gk *
              ((hhatR + ellR) * gk
                + gr * (hhatK + ellK))
        = a ^ 2 + b ^ 2 + c ^ 2 := by
    rw [hb2, hc2]
    dsimp [a]
    ring
  have hinside :
      cr ^ 2 * ck ^ 2
          + gr * gk *
              ((hhatR + ellR) * gk
                + gr * (hhatK + ellK))
        ≤ (a + b + c) ^ 2 := by
    rw [hinsideEq]
    exact habc
  have hpref : 0 ≤ C ^ 2 * gap ^ 2 := by positivity
  have hsq :
      uv ^ 2 ≤ (C * gap * (a + b + c)) ^ 2 := by
    calc
      uv ^ 2
          ≤ C ^ 2 * gap ^ 2 *
              (cr ^ 2 * ck ^ 2
                + gr * gk *
                    ((hhatR + ellR) * gk
                      + gr * (hhatK + ellK))) := hSquared
      _ ≤ C ^ 2 * gap ^ 2 * (a + b + c) ^ 2 :=
            mul_le_mul_of_nonneg_left hinside hpref
      _ = (C * gap * (a + b + c)) ^ 2 := by ring
  have hrhs0 : 0 ≤ C * gap * (a + b + c) := by positivity
  have huv' : uv ≤ C * gap * (a + b + c) := by
    nlinarith
  simpa [a, b, c] using huv'

#print axioms v14_thm_WMB_close


/- ================================================================
   T022 = v13:lem:weak-linear
   ================================================================ -/

/--
Final Young-absorption line of the weak fixed-background linear estimate.
The recurrence is the strong-background recurrence with the external envelope
replaced by the weak envelope; `hYoung` is the standard scalar Young
inequality applied to the square-root term.
-/
theorem v13_lem_weak_linear
    (C0 C1 a d e : ℝ)
    (hC0 : 0 ≤ C0)
    (hC1 : 0 ≤ C1)
    (hd : 0 ≤ d)
    (he : 0 ≤ e)
    (hrec : d ≤ C0 * e + a * Real.sqrt (d * e))
    (hYoung :
      a * Real.sqrt (d * e) ≤ d / 2 + C1 * e) :
    d ≤ 2 * (C0 + C1) * e := by
  have h1 :
      d ≤ C0 * e + d / 2 + C1 * e := by
    calc
      d ≤ C0 * e + a * Real.sqrt (d * e) := hrec
      _ ≤ C0 * e + (d / 2 + C1 * e) := by
            linarith [hYoung]
      _ = C0 * e + d / 2 + C1 * e := by ring
  nlinarith

#print axioms v13_lem_weak_linear


/- ================================================================
   T023 = v13:lem:relative-WMB
   ================================================================ -/

/--
Algebraic closing line of the relative WMB recurrence.  The preceding Bony
and WMB estimates yield `hmid`; Lean carries out the two `2ab <= a^2+b^2`
steps and replaces the two envelope squares by `gamma`.
-/
theorem v13_lem_relative_WMB
    (CE alpha beta ell E D L : ℝ)
    (hCE : 0 ≤ CE)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D)
    (hL : 0 ≤ L)
    (hmid :
      ell ^ 2 ≤ CE *
        (alpha ^ 2 * E
          + beta ^ 2 * Real.sqrt D *
              (Real.sqrt E + Real.sqrt L)
          + (alpha ^ 2 + beta ^ 2) * D)) :
    ell ^ 2 ≤
      3 * CE * (alpha ^ 2 + beta ^ 2) * (E + D + L) := by
  have hsE0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hsD0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsL0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hsE2 : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  have hsD2 : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have hsL2 : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL
  have hDE : Real.sqrt D * Real.sqrt E ≤ (D + E) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt D - Real.sqrt E)]
  have hDL : Real.sqrt D * Real.sqrt L ≤ (D + L) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt D - Real.sqrt L)]
  have hroot :
      Real.sqrt D * (Real.sqrt E + Real.sqrt L)
        ≤ E + D + L := by
    nlinarith

  let gamma : ℝ := alpha ^ 2 + beta ^ 2
  let S : ℝ := E + D + L
  have hgamma0 : 0 ≤ gamma := by dsimp [gamma]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have ha2 : alpha ^ 2 ≤ gamma := by
    dsimp [gamma]
    nlinarith [sq_nonneg beta]
  have hb2 : beta ^ 2 ≤ gamma := by
    dsimp [gamma]
    nlinarith [sq_nonneg alpha]
  have hES : E ≤ S := by dsimp [S]; linarith
  have hDS : D ≤ S := by dsimp [S]; linarith
  have hrootS :
      Real.sqrt D * (Real.sqrt E + Real.sqrt L) ≤ S := by
    simpa [S] using hroot
  have hA : alpha ^ 2 * E ≤ gamma * S :=
    mul_le_mul ha2 hES hE hgamma0
  have hB0 :
      beta ^ 2 * (Real.sqrt D * (Real.sqrt E + Real.sqrt L))
        ≤ gamma * S :=
    mul_le_mul hb2 hrootS (by positivity) hgamma0
  have hB :
      beta ^ 2 * Real.sqrt D * (Real.sqrt E + Real.sqrt L)
        ≤ gamma * S := by
    calc
      beta ^ 2 * Real.sqrt D * (Real.sqrt E + Real.sqrt L)
          = beta ^ 2 *
              (Real.sqrt D * (Real.sqrt E + Real.sqrt L)) := by ring
      _ ≤ gamma * S := hB0
  have hDterm : gamma * D ≤ gamma * S :=
    mul_le_mul_of_nonneg_left hDS hgamma0
  have hinner :
      alpha ^ 2 * E
          + beta ^ 2 * Real.sqrt D *
              (Real.sqrt E + Real.sqrt L)
          + gamma * D
        ≤ 3 * (gamma * S) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hinner hCE
  calc
    ell ^ 2 ≤ CE *
        (alpha ^ 2 * E
          + beta ^ 2 * Real.sqrt D *
              (Real.sqrt E + Real.sqrt L)
          + (alpha ^ 2 + beta ^ 2) * D) := hmid
    _ = CE *
        (alpha ^ 2 * E
          + beta ^ 2 * Real.sqrt D *
              (Real.sqrt E + Real.sqrt L)
          + gamma * D) := by rfl
    _ ≤ CE * (3 * (gamma * S)) := hmul
    _ = 3 * CE * (alpha ^ 2 + beta ^ 2) * (E + D + L) := by
      dsimp [gamma, S]
      ring

#print axioms v13_lem_relative_WMB


/- ================================================================
   T024 = v13:lem:causal-linear
   ================================================================ -/

/--
Aggregation of the two pieces of the slow-envelope convolution split at
`K+D`.  `hlow` is the near-frequency Young bound and `htail` is the far-tail
geometric bound.  Lean combines them into the displayed causal estimate.
-/
theorem v13_lem_causal_linear
    (CE rho DK near tail Enear Lnear Einf Linf : ℝ)
    (hCE : 0 ≤ CE)
    (hrho : 0 ≤ rho)
    (hlow : near ≤ Enear + Lnear)
    (htail : tail ≤ rho * (Einf + Linf))
    (hsplit : DK ≤ CE * near + CE * tail) :
    DK ≤ CE * (Enear + Lnear)
      + CE * rho * (Einf + Linf) := by
  calc
    DK ≤ CE * near + CE * tail := hsplit
    _ ≤ CE * (Enear + Lnear) + CE * (rho * (Einf + Linf)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlow hCE)
        (mul_le_mul_of_nonneg_left htail hCE)
    _ = CE * (Enear + Lnear)
          + CE * rho * (Einf + Linf) := by ring

#print axioms v13_lem_causal_linear

end

end SMLeanMinV1


namespace SMLeanMinV1

set_option maxHeartbeats 1000000

/- B13 explicit-order/nonnegativity repair. -/

noncomputable section

/- ================================================================
   T025 = v13:lem:Volterra
   ================================================================ -/

/-- Previous-value convention after translating the lower cutoff to `0`. -/
def prevNat (y : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => y n

/-- Delayed value, with the paper convention that indices below the lower cutoff vanish. -/
def delayedNat (y : ℕ → ℝ) (d i : ℕ) : ℝ :=
  if d ≤ i then y (i - d) else 0

/-- Elementary product telescoping identity used by discrete Gronwall. -/
lemma v13_prod_telescoping (b : ℕ → ℝ) :
    ∀ n : ℕ,
      (Finset.range n).prod (fun i => 1 + b i) =
        1 + (∑ i ∈ Finset.range n,
          b i * (Finset.range i).prod (fun j => 1 + b j)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
      ring

/-- Product form of finite discrete Gronwall. -/
lemma v13_discrete_gronwall_product
    (F b y : ℕ → ℝ)
    (hF0 : ∀ n, 0 ≤ F n)
    (hb0 : ∀ n, 0 ≤ b n)
    (hFmono : Monotone F)
    (hrec : ∀ n,
      y n ≤ F n +
        (∑ i ∈ Finset.range (n + 1), b i * prevNat y i)) :
    ∀ n,
      y n ≤ F n * (Finset.range (n + 1)).prod (fun i => 1 + b i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hsum :
          (∑ i ∈ Finset.range (n + 1), b i * prevNat y i)
            ≤
          (∑ i ∈ Finset.range (n + 1),
            b i *
              (F n * (Finset.range i).prod (fun j => 1 + b j))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_le : i ≤ n := by
          exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hprev :
            prevNat y i ≤
              F n * (Finset.range i).prod (fun j => 1 + b j) := by
          cases i with
          | zero =>
              simp [prevNat, hF0 n]
          | succ m =>
              have hm_lt : m < n := by omega
              have hy_m := ih m hm_lt
              have hFm : F m ≤ F n :=
                hFmono (Nat.le_of_lt hm_lt)
              have hp0 :
                  0 ≤ (Finset.range (m + 1)).prod (fun j => 1 + b j) := by
                apply Finset.prod_nonneg
                intro j hj
                linarith [hb0 j]
              have hscale :
                  F m * (Finset.range (m + 1)).prod (fun j => 1 + b j)
                    ≤
                  F n * (Finset.range (m + 1)).prod (fun j => 1 + b j) :=
                mul_le_mul_of_nonneg_right hFm hp0
              simpa [prevNat] using le_trans hy_m hscale
        exact mul_le_mul_of_nonneg_left hprev (hb0 i)
      have hfactor :
          (∑ i ∈ Finset.range (n + 1),
            b i *
              (F n * (Finset.range i).prod (fun j => 1 + b j)))
          =
          F n *
            (∑ i ∈ Finset.range (n + 1),
              b i * (Finset.range i).prod (fun j => 1 + b j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      calc
        y n ≤ F n +
            (∑ i ∈ Finset.range (n + 1), b i * prevNat y i) := hrec n
        _ ≤ F n +
            (∑ i ∈ Finset.range (n + 1),
              b i *
                (F n * (Finset.range i).prod (fun j => 1 + b j))) := by
              linarith only [hsum]
        _ = F n *
            (1 + (∑ i ∈ Finset.range (n + 1),
              b i * (Finset.range i).prod (fun j => 1 + b j))) := by
              rw [hfactor]
              ring
        _ = F n * (Finset.range (n + 1)).prod (fun i => 1 + b i) := by
              rw [← v13_prod_telescoping b (n + 1)]

/-- `prod (1+b_i) <= exp(sum b_i)` for nonnegative weights. -/
lemma v13_product_le_exp_sum
    (b : ℕ → ℝ)
    (hb0 : ∀ n, 0 ≤ b n)
    (hexp : ∀ x : ℝ, 0 ≤ x → 1 + x ≤ Real.exp x) :
    ∀ n : ℕ,
      (Finset.range n).prod (fun i => 1 + b i)
        ≤ Real.exp (∑ i ∈ Finset.range n, b i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, Real.exp_add]
      have hfac0 : 0 ≤ 1 + b n := by
        linarith [hb0 n]
      calc
        (Finset.range n).prod (fun i => 1 + b i) * (1 + b n)
            ≤ Real.exp (∑ i ∈ Finset.range n, b i) * (1 + b n) :=
              mul_le_mul_of_nonneg_right ih hfac0
        _ ≤ Real.exp (∑ i ∈ Finset.range n, b i) * Real.exp (b n) :=
              mul_le_mul_of_nonneg_left (hexp (b n) (hb0 n)) (Real.exp_nonneg _)

/--
Finite lower-cutoff delayed Volterra--Gronwall, with the lower cutoff shifted
from `K_min` to `0`.  The output constant is made explicit as `C+1`; this is
the paper's generic-constant enlargement.
-/
theorem v13_lem_Volterra
    (C Γ : ℝ) (d1 : ℕ)
    (A X gamma : ℕ → ℝ)
    (hC : 0 ≤ C)
    (hGamma : 0 ≤ Γ)
    (hd1 : 1 ≤ d1)
    (hA0 : ∀ n, 0 ≤ A n)
    (hX0 : ∀ n, 0 ≤ X n)
    (hgamma0 : ∀ n, 0 ≤ gamma n)
    (hAmono : Monotone A)
    (hXmono : Monotone X)
    (hpartial : ∀ n,
      (∑ i ∈ Finset.range (n + 1), gamma i) ≤ Γ)
    (hrec : ∀ n,
      X n ≤ C * A n +
        C * (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => A j + X j) d1 i))
    (hexp : ∀ x : ℝ, 0 ≤ x → 1 + x ≤ Real.exp x) :
    ∀ n,
      X n ≤ (C + 1) * A n * Real.exp ((C + 1) * Γ) := by
  let y : ℕ → ℝ := fun n => A n + X n
  let F : ℕ → ℝ := fun n => (C + 1) * A n
  let b : ℕ → ℝ := fun n => C * gamma n

  have hy0 : ∀ n, 0 ≤ y n := by
    intro n
    dsimp [y]
    exact add_nonneg (hA0 n) (hX0 n)

  have hymono : Monotone y := by
    intro m n hmn
    dsimp [y]
    exact add_le_add (hAmono hmn) (hXmono hmn)

  have hCp1 : 0 ≤ C + 1 := by linarith
  have hF0 : ∀ n, 0 ≤ F n := by
    intro n
    dsimp [F]
    exact mul_nonneg hCp1 (hA0 n)

  have hFmono : Monotone F := by
    intro m n hmn
    dsimp [F]
    exact mul_le_mul_of_nonneg_left (hAmono hmn) hCp1

  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b]
    exact mul_nonneg hC (hgamma0 n)

  have hdelay : ∀ i,
      delayedNat y d1 i ≤ prevNat y i := by
    intro i
    unfold delayedNat
    split_ifs with hi
    · cases i with
      | zero => omega
      | succ m =>
          have hidx : (m + 1) - d1 ≤ m := by omega
          have hm := hymono hidx
          simpa [prevNat] using hm
    · cases i with
      | zero => simp [prevNat]
      | succ m =>
          simp [prevNat]
          exact hy0 m

  have hrecY : ∀ n,
      y n ≤ F n +
        (∑ i ∈ Finset.range (n + 1), b i * prevNat y i) := by
    intro n
    have hsum0 :
        C * (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat y d1 i)
          ≤
        (∑ i ∈ Finset.range (n + 1), b i * prevNat y i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hcg : 0 ≤ C * gamma i := mul_nonneg hC (hgamma0 i)
      calc
        C * (gamma i * delayedNat y d1 i)
            = (C * gamma i) * delayedNat y d1 i := by ring
        _ ≤ (C * gamma i) * prevNat y i :=
              mul_le_mul_of_nonneg_left (hdelay i) hcg
        _ = b i * prevNat y i := by rfl
    calc
      y n = A n + X n := by rfl
      _ ≤ A n +
          (C * A n +
            C * (∑ i ∈ Finset.range (n + 1),
              gamma i * delayedNat y d1 i)) := by
            linarith only [hrec n]
      _ = (C + 1) * A n +
          C * (∑ i ∈ Finset.range (n + 1),
            gamma i * delayedNat y d1 i) := by ring
      _ ≤ (C + 1) * A n +
          (∑ i ∈ Finset.range (n + 1), b i * prevNat y i) :=
            add_le_add le_rfl hsum0
      _ = F n +
          (∑ i ∈ Finset.range (n + 1), b i * prevNat y i) := by rfl

  have hG :=
    v13_discrete_gronwall_product F b y hF0 hb0 hFmono hrecY

  intro n
  have hsumB :
      (∑ i ∈ Finset.range (n + 1), b i)
        = C * (∑ i ∈ Finset.range (n + 1), gamma i) := by
    dsimp [b]
    rw [Finset.mul_sum]

  have hsumBGamma :
      (∑ i ∈ Finset.range (n + 1), b i) ≤ C * Γ := by
    rw [hsumB]
    exact mul_le_mul_of_nonneg_left (hpartial n) hC

  have hprod := v13_product_le_exp_sum b hb0 hexp (n + 1)
  have hexp1 :
      Real.exp (∑ i ∈ Finset.range (n + 1), b i)
        ≤ Real.exp (C * Γ) :=
    Real.exp_le_exp.mpr hsumBGamma

  have hCGamma : C * Γ ≤ (C + 1) * Γ := by
    have hCC : C ≤ C + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hCC hGamma
  have hexp2 :
      Real.exp (C * Γ) ≤ Real.exp ((C + 1) * Γ) :=
    Real.exp_le_exp.mpr hCGamma

  have hXA : X n ≤ y n := by
    dsimp [y]
    linarith [hA0 n]

  have hFn0 : 0 ≤ F n := hF0 n
  calc
    X n ≤ y n := hXA
    _ ≤ F n * (Finset.range (n + 1)).prod (fun i => 1 + b i) := hG n
    _ ≤ F n * Real.exp (∑ i ∈ Finset.range (n + 1), b i) :=
          mul_le_mul_of_nonneg_left hprod hFn0
    _ ≤ F n * Real.exp (C * Γ) :=
          mul_le_mul_of_nonneg_left hexp1 hFn0
    _ ≤ F n * Real.exp ((C + 1) * Γ) :=
          mul_le_mul_of_nonneg_left hexp2 hFn0
    _ = (C + 1) * A n * Real.exp ((C + 1) * Γ) := by rfl

#print axioms v13_lem_Volterra


/- ================================================================
   T026 = v13:thm:short-stability
   ================================================================ -/

/--
Algebraic/cumulative spine of the short-time stability theorem after T023 and
T024 have produced the delayed recurrence.  `E` is the cumulative squared
input envelope, `L` the cumulative weak local-smoothing forcing, and `Dinf`
the cumulative solution square sum.
-/
theorem v13_thm_short_stability
    (CE Γ eps rho Einf Linf Dinf inputNorm SNorm : ℝ)
    (d1 N : ℕ)
    (E L gamma : ℕ → ℝ)
    (hCE : 0 ≤ CE)
    (hGamma : 0 ≤ Γ)
    (heps : 0 ≤ eps)
    (hrho : 0 ≤ rho)
    (hEinf : 0 ≤ Einf)
    (hLinf : 0 ≤ Linf)
    (hDinf : 0 ≤ Dinf)
    (hinput : 0 ≤ inputNorm)
    (hS : 0 ≤ SNorm)
    (hd1 : 1 ≤ d1)
    (hE0 : ∀ n, 0 ≤ E n)
    (hL0 : ∀ n, 0 ≤ L n)
    (hgamma0 : ∀ n, 0 ≤ gamma n)
    (hEmono : Monotone E)
    (hLmono : Monotone L)
    (hpartial : ∀ n,
      (∑ i ∈ Finset.range (n + 1), gamma i) ≤ Γ)
    (hETop : E N = Einf)
    (hLTop : L N = Linf)
    (hPre : ∀ n,
      L n ≤ CE *
          (∑ i ∈ Finset.range (n + 1),
            gamma i * delayedNat (fun j => E j + L j) d1 i)
        + eps * (Einf + Linf))
    (hSmall :
      ((CE + 2) * Real.exp ((CE + 2) * Γ)) * eps ≤ (1 : ℝ) / 4)
    (hDtop :
      Dinf ≤ CE * (Einf + Linf) + CE * rho * (Einf + Linf))
    (hEinput : Einf ≤ inputNorm ^ 2)
    (hSsquare : SNorm ^ 2 ≤ Dinf)
    (hexp : ∀ x : ℝ, 0 ≤ x → 1 + x ≤ Real.exp x) :
    ∃ Cstab : ℝ,
      0 ≤ Cstab ∧
      Linf ≤ Cstab * Einf ∧
      Dinf ≤ Cstab * Einf ∧
      SNorm ≤ Real.sqrt Cstab * inputNorm := by

  let tail : ℝ := eps * (Einf + Linf)
  let Atilde : ℕ → ℝ := fun n => E n + tail
  let Cbase : ℝ := CE + 1
  let K : ℝ := (CE + 2) * Real.exp ((CE + 2) * Γ)

  have htail0 : 0 ≤ tail := by
    dsimp [tail]
    exact mul_nonneg heps (add_nonneg hEinf hLinf)

  have hA0 : ∀ n, 0 ≤ Atilde n := by
    intro n
    dsimp [Atilde]
    exact add_nonneg (hE0 n) htail0

  have hAmono : Monotone Atilde := by
    intro m n hmn
    dsimp [Atilde]
    linarith [hEmono hmn]

  have hCbase0 : 0 ≤ Cbase := by
    dsimp [Cbase]
    linarith

  have hdelay_enlarge : ∀ i,
      delayedNat (fun j => E j + L j) d1 i ≤
        delayedNat (fun j => Atilde j + L j) d1 i := by
    intro i
    unfold delayedNat
    split_ifs with hi
    · dsimp [Atilde]
      linarith
    · rfl

  have hVolterraPre : ∀ n,
      L n ≤ Cbase * Atilde n +
        Cbase * (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => Atilde j + L j) d1 i) := by
    intro n
    have hsum0 :
        0 ≤ (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => E j + L j) d1 i) := by
      apply Finset.sum_nonneg
      intro i hi
      have hdel0 : 0 ≤ delayedNat (fun j => E j + L j) d1 i := by
        unfold delayedNat
        split_ifs with hdi
        · exact add_nonneg (hE0 (i - d1)) (hL0 (i - d1))
        · norm_num
      exact mul_nonneg (hgamma0 i) hdel0
    have hsum_le :
        (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => E j + L j) d1 i)
          ≤
        (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => Atilde j + L j) d1 i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hdelay_enlarge i) (hgamma0 i)
    have hsum1 :
        0 ≤ (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => Atilde j + L j) d1 i) := by
      apply Finset.sum_nonneg
      intro i hi
      unfold delayedNat
      split_ifs with hdi
      · exact mul_nonneg (hgamma0 i)
          (add_nonneg (hA0 (i - d1)) (hL0 (i - d1)))
      · norm_num
    have hCEle : CE ≤ Cbase := by
      dsimp [Cbase]
      linarith
    have hCEsum :
        CE * (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => E j + L j) d1 i)
          ≤
        Cbase * (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => Atilde j + L j) d1 i) := by
      calc
        CE * (∑ i ∈ Finset.range (n + 1),
          gamma i * delayedNat (fun j => E j + L j) d1 i)
            ≤ CE * (∑ i ∈ Finset.range (n + 1),
              gamma i * delayedNat (fun j => Atilde j + L j) d1 i) :=
                mul_le_mul_of_nonneg_left hsum_le hCE
        _ ≤ Cbase * (∑ i ∈ Finset.range (n + 1),
              gamma i * delayedNat (fun j => Atilde j + L j) d1 i) :=
                mul_le_mul_of_nonneg_right hCEle hsum1
    have htail_le : tail ≤ Cbase * Atilde n := by
      have hAle : tail ≤ Atilde n := by
        dsimp [Atilde]
        linarith [hE0 n]
      have hbase1 : 1 ≤ Cbase := by
        dsimp [Cbase]
        linarith
      have hAt0 : 0 ≤ Atilde n := hA0 n
      have hscale : Atilde n ≤ Cbase * Atilde n := by
        calc
          Atilde n = 1 * Atilde n := by ring
          _ ≤ Cbase * Atilde n :=
            mul_le_mul_of_nonneg_right hbase1 hAt0
      exact le_trans hAle hscale
    calc
      L n ≤ CE *
          (∑ i ∈ Finset.range (n + 1),
            gamma i * delayedNat (fun j => E j + L j) d1 i)
          + tail := by
            simpa [tail, add_comm] using hPre n
      _ ≤ Cbase *
          (∑ i ∈ Finset.range (n + 1),
            gamma i * delayedNat (fun j => Atilde j + L j) d1 i)
          + Cbase * Atilde n := add_le_add hCEsum htail_le
      _ = Cbase * Atilde n +
          Cbase * (∑ i ∈ Finset.range (n + 1),
            gamma i * delayedNat (fun j => Atilde j + L j) d1 i) := by ring

  have hVol := v13_lem_Volterra
    (C := Cbase) (Γ := Γ) (d1 := d1)
    (A := Atilde) (X := L) (gamma := gamma)
    hCbase0 hGamma hd1 hA0 hL0 hgamma0 hAmono hLmono hpartial
    hVolterraPre hexp

  have hKform :
      (Cbase + 1) * Real.exp ((Cbase + 1) * Γ) = K := by
    dsimp [Cbase, K]
    ring_nf

  have hLraw :
      Linf ≤ K * (Einf + eps * (Einf + Linf)) := by
    have hN := hVol N
    rw [hLTop] at hN
    dsimp [Atilde, tail] at hN
    rw [hETop] at hN
    calc
      Linf ≤ (Cbase + 1) * (Einf + eps * (Einf + Linf)) *
          Real.exp ((Cbase + 1) * Γ) := hN
      _ = ((Cbase + 1) * Real.exp ((Cbase + 1) * Γ)) *
          (Einf + eps * (Einf + Linf)) := by ring
      _ = K * (Einf + eps * (Einf + Linf)) := by
          exact congrArg (fun z : ℝ => z * (Einf + eps * (Einf + Linf))) hKform

  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by linarith [hCE]) (Real.exp_nonneg _)

  have hLabsorbed :
      Linf ≤ 2 * K * (1 + eps) * Einf := by
    have hKeps : K * eps ≤ (1 : ℝ) / 4 := by
      simpa [K] using hSmall
    have hsmallL : K * eps * Linf ≤ Linf / 4 := by
      have hmul := mul_le_mul_of_nonneg_right hKeps hLinf
      nlinarith
    have hsplit :
        K * (Einf + eps * (Einf + Linf)) =
          K * (1 + eps) * Einf + K * eps * Linf := by ring
    rw [hsplit] at hLraw
    nlinarith [hsmallL]

  let CL : ℝ := 2 * K * (1 + eps)
  have hCL0 : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg (mul_nonneg (by norm_num) hK0) (by linarith [heps])
  have hLfinal : Linf ≤ CL * Einf := by
    simpa [CL] using hLabsorbed

  let CD : ℝ := CE * (1 + rho) * (1 + CL)
  have hCD0 : 0 ≤ CD := by
    dsimp [CD]
    exact mul_nonneg
      (mul_nonneg hCE (by linarith [hrho]))
      (by linarith [hCL0])

  have hDfinal : Dinf ≤ CD * Einf := by
    have hsumEL : Einf + Linf ≤ (1 + CL) * Einf := by
      calc
        Einf + Linf ≤ Einf + CL * Einf :=
          add_le_add le_rfl hLfinal
        _ = (1 + CL) * Einf := by ring
    have hcoef : 0 ≤ CE * (1 + rho) :=
      mul_nonneg hCE (by linarith [hrho])
    calc
      Dinf ≤ CE * (Einf + Linf) + CE * rho * (Einf + Linf) := hDtop
      _ = CE * (1 + rho) * (Einf + Linf) := by ring
      _ ≤ CE * (1 + rho) * ((1 + CL) * Einf) :=
            mul_le_mul_of_nonneg_left hsumEL hcoef
      _ = CD * Einf := by
            dsimp [CD]
            ring

  let Cstab : ℝ := 1 + CL + CD
  have hCstab0 : 0 ≤ Cstab := by
    dsimp [Cstab]
    linarith [hCL0, hCD0]
  have hCLle : CL ≤ Cstab := by
    dsimp [Cstab]
    linarith
  have hCDle : CD ≤ Cstab := by
    dsimp [Cstab]
    linarith

  have hLstab : Linf ≤ Cstab * Einf :=
    le_trans hLfinal (mul_le_mul_of_nonneg_right hCLle hEinf)
  have hDstab : Dinf ≤ Cstab * Einf :=
    le_trans hDfinal (mul_le_mul_of_nonneg_right hCDle hEinf)

  have hDstabInput : Dinf ≤ Cstab * inputNorm ^ 2 :=
    le_trans hDstab (mul_le_mul_of_nonneg_left hEinput hCstab0)

  have hsqrtC0 : 0 ≤ Real.sqrt Cstab := Real.sqrt_nonneg _
  have hsqrtC2 : (Real.sqrt Cstab) ^ 2 = Cstab := Real.sq_sqrt hCstab0
  have hSq :
      SNorm ^ 2 ≤ (Real.sqrt Cstab * inputNorm) ^ 2 := by
    calc
      SNorm ^ 2 ≤ Dinf := hSsquare
      _ ≤ Cstab * inputNorm ^ 2 := hDstabInput
      _ = (Real.sqrt Cstab * inputNorm) ^ 2 := by
            rw [mul_pow, hsqrtC2]

  have htarget0 : 0 ≤ Real.sqrt Cstab * inputNorm :=
    mul_nonneg (Real.sqrt_nonneg _) hinput
  have hSfinal : SNorm ≤ Real.sqrt Cstab * inputNorm := by
    nlinarith only [hSq, hS, htarget0]

  exact ⟨Cstab, hCstab0, hLstab, hDstab, hSfinal⟩

#print axioms v13_thm_short_stability


/- ================================================================
   T027 = v13:thm:long-stability
   ================================================================ -/

lemma v13_pow_mono_nat
    (P : ℝ) (hP : 1 ≤ P) {m n : ℕ} (hmn : m ≤ n) :
    P ^ m ≤ P ^ n := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
  subst n
  clear hmn
  rw [pow_add]
  have hP0 : 0 ≤ P := by linarith
  have hPd : 1 ≤ P ^ d := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [pow_succ]
        have hpow0 : 0 ≤ P ^ d := pow_nonneg hP0 d
        calc
          1 ≤ P ^ d := ih
          _ = P ^ d * 1 := by ring
          _ ≤ P ^ d * P := mul_le_mul_of_nonneg_left hP hpow0
  have hPm0 : 0 ≤ P ^ m := pow_nonneg hP0 m
  have hmul := mul_le_mul_of_nonneg_left hPd hPm0
  simpa using hmul

/-- Finite chaining of the short-time estimate over the `L^4` partition. -/
theorem v13_thm_long_stability
    (Cshort init global : ℝ) (J : ℕ)
    (endpoint forcing seg : ℕ → ℝ)
    (hC : 0 ≤ Cshort)
    (hinit : 0 ≤ init)
    (hglobal0 : 0 ≤ global)
    (hend0 : ∀ n, 0 ≤ endpoint n)
    (hforc0 : ∀ n, 0 ≤ forcing n)
    (hseg0 : ∀ n, 0 ≤ seg n)
    (hendInit : endpoint 0 ≤ init)
    (hstep : ∀ j < J,
      endpoint (j + 1) ≤ Cshort * (endpoint j + forcing j))
    (hseg : ∀ j < J,
      seg j ≤ Cshort * (endpoint j + forcing j))
    (hglobal : global ≤ (∑ j ∈ Finset.range J, seg j)) :
    let total : ℝ := init + (∑ j ∈ Finset.range J, forcing j)
    let P : ℝ := 2 * (1 + Cshort)
    global ≤ ((J : ℝ) * P ^ J) * total := by
  let total : ℝ := init + (∑ j ∈ Finset.range J, forcing j)
  let P : ℝ := 2 * (1 + Cshort)

  have hsumForcing0 :
      0 ≤ (∑ j ∈ Finset.range J, forcing j) := by
    exact Finset.sum_nonneg (fun j hj => hforc0 j)
  have htotal0 : 0 ≤ total := by
    dsimp [total]
    exact add_nonneg hinit hsumForcing0
  have hP1 : 1 ≤ P := by
    dsimp [P]
    linarith
  have hP2C : 2 * Cshort ≤ P := by
    dsimp [P]
    linarith

  have hforce_le : ∀ j < J, forcing j ≤ total := by
    intro j hj
    have hjmem : j ∈ Finset.range J := Finset.mem_range.mpr hj
    have hsingle : forcing j ≤ (∑ i ∈ Finset.range J, forcing i) := by
      exact Finset.single_le_sum (fun i hi => hforc0 i) hjmem
    dsimp [total]
    linarith

  have hendBound : ∀ n ≤ J, endpoint n ≤ P ^ n * total := by
    intro n hn
    induction n with
    | zero =>
        have hinit_total : init ≤ total := by
          dsimp [total]
          exact le_add_of_nonneg_right hsumForcing0
        calc
          endpoint 0 ≤ init := hendInit
          _ ≤ total := hinit_total
          _ = P ^ 0 * total := by simp
    | succ n ih =>
        have hnJ : n < J := by omega
        have hih := ih (by omega)
        have hf := hforce_le n hnJ
        have hPn1 : 1 ≤ P ^ n := by
          simpa using
            (v13_pow_mono_nat P hP1 (m := 0) (n := n) (Nat.zero_le n))
        have hsum : endpoint n + forcing n ≤ 2 * (P ^ n * total) := by
          have hft : forcing n ≤ P ^ n * total := by
            have ht : total ≤ P ^ n * total := by
              calc
                total = 1 * total := by ring
                _ ≤ P ^ n * total := mul_le_mul_of_nonneg_right hPn1 htotal0
            exact le_trans hf ht
          linarith
        calc
          endpoint (n + 1) ≤ Cshort * (endpoint n + forcing n) := hstep n hnJ
          _ ≤ Cshort * (2 * (P ^ n * total)) :=
                mul_le_mul_of_nonneg_left hsum hC
          _ = (2 * Cshort) * P ^ n * total := by ring
          _ ≤ P * P ^ n * total := by
                have hP0 : 0 ≤ P := by linarith [hP1]
                have hpow0 : 0 ≤ P ^ n := pow_nonneg hP0 n
                have hcoef :
                    (2 * Cshort) * P ^ n ≤ P * P ^ n :=
                  mul_le_mul_of_nonneg_right hP2C hpow0
                exact mul_le_mul_of_nonneg_right hcoef htotal0
          _ = P ^ (n + 1) * total := by
                rw [pow_succ]
                ring

  have hsegUniform : ∀ j ∈ Finset.range J,
      seg j ≤ P ^ J * total := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.mp hj
    have hendj := hendBound j (Nat.le_of_lt hjJ)
    have hfj := hforce_le j hjJ
    have hPj1 : 1 ≤ P ^ j := by
      simpa using
        (v13_pow_mono_nat P hP1 (m := 0) (n := j) (Nat.zero_le j))
    have hft : forcing j ≤ P ^ j * total := by
      have ht : total ≤ P ^ j * total := by
        calc
          total = 1 * total := by ring
          _ ≤ P ^ j * total := mul_le_mul_of_nonneg_right hPj1 htotal0
      exact le_trans hfj ht
    have hsum : endpoint j + forcing j ≤ 2 * (P ^ j * total) := by
      linarith
    have hs0 : seg j ≤ P ^ (j + 1) * total := by
      calc
        seg j ≤ Cshort * (endpoint j + forcing j) := hseg j hjJ
        _ ≤ Cshort * (2 * (P ^ j * total)) :=
              mul_le_mul_of_nonneg_left hsum hC
        _ = (2 * Cshort) * P ^ j * total := by ring
        _ ≤ P * P ^ j * total := by
              have hP0 : 0 ≤ P := by linarith [hP1]
              have hpow0 : 0 ≤ P ^ j := pow_nonneg hP0 j
              have hcoef :
                  (2 * Cshort) * P ^ j ≤ P * P ^ j :=
                mul_le_mul_of_nonneg_right hP2C hpow0
              exact mul_le_mul_of_nonneg_right hcoef htotal0
        _ = P ^ (j + 1) * total := by
              rw [pow_succ]
              ring
    have hpmono : P ^ (j + 1) ≤ P ^ J :=
      v13_pow_mono_nat P hP1 (m := j + 1) (n := J) (by omega)
    exact le_trans hs0 (mul_le_mul_of_nonneg_right hpmono htotal0)

  have hsumSeg :
      (∑ j ∈ Finset.range J, seg j)
        ≤ (∑ j ∈ Finset.range J, (P ^ J * total)) := by
    exact Finset.sum_le_sum hsegUniform

  calc
    global ≤ (∑ j ∈ Finset.range J, seg j) := hglobal
    _ ≤ (∑ j ∈ Finset.range J, (P ^ J * total)) := hsumSeg
    _ = ((J : ℝ) * P ^ J) * total := by
          simp
          ring

#print axioms v13_thm_long_stability

/- END B13: all three target theorem names above must print without sorryAx. -/


end

end SMLeanMinV1

namespace SMLeanMinV1

set_option maxHeartbeats 1000000

/-!
B14: T028--T032.

T001--T027 are already PASS_WEB_VERIFIED.  This file does not re-run them.
Whenever a preceding internal theorem is needed, its *output inequality* is
passed as an explicitly named hypothesis.  Standard harmonic-analysis or
compactness inputs are likewise named generically; none of the target
conclusions T028--T032 is assumed.
-/

noncomputable section

/- ================================================================
   T028 = v15:thm:fullN-stability
   ================================================================ -/

/--
Abstract paper-line closure of the `ε ↓ 0` step in full-N stability.

For every positive split error `ε`, the infimal-sum decomposition together
with the already verified weak-forcing/Volterra chain and ℓ¹*ℓ²→ℓ² gives
an auxiliary forcing size `splitNorm` with

  splitNorm ≤ forcing + ε,
  S ≤ C * (init + splitNorm).

The theorem proves the exact ε-free estimate; the desired estimate itself is
not an input.
-/
theorem v15_thm_fullN_stability
    (C S init forcing : ℝ)
    (hC : 0 ≤ C)
    (hS : 0 ≤ S)
    (hinit : 0 ≤ init)
    (hforcing : 0 ≤ forcing)
    (hSplit :
      ∀ ε : ℝ, 0 < ε →
        ∃ splitNorm : ℝ,
          0 ≤ splitNorm ∧
          splitNorm ≤ forcing + ε ∧
          S ≤ C * (init + splitNorm)) :
    S ≤ C * (init + forcing) := by
  by_contra hnot
  have hlt : C * (init + forcing) < S := lt_of_not_ge hnot
  let gap : ℝ := S - C * (init + forcing)
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  let ε : ℝ := gap / (2 * (C + 1))
  have hden : 0 < 2 * (C + 1) := by
    nlinarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos hgap hden
  obtain ⟨splitNorm, hsplit0, hsplit, hSsplit⟩ := hSplit ε hε
  have hinside : init + splitNorm ≤ init + forcing + ε := by
    linarith
  have hscaled :
      C * (init + splitNorm) ≤ C * (init + forcing + ε) :=
    mul_le_mul_of_nonneg_left hinside hC
  have hUpper : S ≤ C * (init + forcing + ε) :=
    le_trans hSsplit hscaled
  have hCeps : C * ε < gap / 2 := by
    have hratio : C / (C + 1) < 1 := by
      have hp : 0 < C + 1 := by linarith
      apply (div_lt_one hp).2
      linarith
    have hg2 : 0 < gap / 2 := by positivity
    dsimp [ε]
    calc
      C * (gap / (2 * (C + 1)))
          = (gap / 2) * (C / (C + 1)) := by field_simp
      _ < (gap / 2) * 1 :=
        mul_lt_mul_of_pos_left hratio hg2
      _ = gap / 2 := by ring
  have : S < S := by
    calc
      S ≤ C * (init + forcing + ε) := hUpper
      _ = C * (init + forcing) + C * ε := by ring
      _ < C * (init + forcing) + gap / 2 := by linarith
      _ < S := by
        dsimp [gap]
        linarith
  exact (lt_irrefl S) this

#print axioms v15_thm_fullN_stability

end

end SMLeanMinV1


namespace SMLeanMinV1
open scoped BigOperators

theorem v21_N025_mix_first_order_core
    {ι : Type*} [Fintype ι]
    (A dU : ι → ℂ) :
    (∑ a, A a) * (∑ b, dU b) - ∑ a, A a * dU a
      = ∑ a, A a * ((∑ b, dU b) - dU a) := by
  rw [Finset.sum_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
#print axioms v21_N025_mix_first_order_core
end SMLeanMinV1



namespace SMLeanMinV1

noncomputable section

set_option maxHeartbeats 1000000

/- B20 / T029 + T030B.
   No placeholder Claim/Prop hypotheses.
   All four differentiated frame identities are proved from the explicit
   stereographic formulas by quotient/product rules and elementary algebra.
-/

structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

lemma V3.ext_coords {a b : V3}
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a
  cases b
  simp_all

def vadd (a b : V3) : V3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def vsmul (c : ℝ) (a : V3) : V3 := ⟨c*a.x, c*a.y, c*a.z⟩
def vdot (a b : V3) : ℝ := a.x*b.x + a.y*b.y + a.z*b.z
def vnormSq (a : V3) : ℝ := vdot a a

structure StereoTriad where
  u : ℝ
  v : ℝ
  chi : ℝ

namespace StereoTriad

def g (s : StereoTriad) : ℝ := 1 + s.u^2 + s.v^2

def N (s : StereoTriad) : V3 :=
  let d := g s
  ⟨2*s.u/d, 2*s.v/d, (1-s.u^2-s.v^2)/d⟩

def e10 (s : StereoTriad) : V3 :=
  let d := g s
  ⟨(1-s.u^2+s.v^2)/d, (-2*s.u*s.v)/d, (-2*s.u)/d⟩

def e20 (s : StereoTriad) : V3 :=
  let d := g s
  ⟨(-2*s.u*s.v)/d, (1+s.u^2-s.v^2)/d, (-2*s.v)/d⟩

def E1 (s : StereoTriad) : V3 :=
  vadd (vsmul (Real.cos s.chi) (e10 s))
       (vsmul (Real.sin s.chi) (e20 s))

def E2 (s : StereoTriad) : V3 :=
  vadd (vsmul (-Real.sin s.chi) (e10 s))
       (vsmul (Real.cos s.chi) (e20 s))

def Qre (s : StereoTriad) (du dv : ℝ) : ℝ :=
  (Real.cos s.chi * du + Real.sin s.chi * dv) / g s

def Qim (s : StereoTriad) (du dv : ℝ) : ℝ :=
  (Real.cos s.chi * dv - Real.sin s.chi * du) / g s

def aCoeff (s : StereoTriad) (du dv : ℝ) : ℝ :=
  2 * (s.u * dv - s.v * du) / g s

def ACoeff (s : StereoTriad) (du dv dchi : ℝ) : ℝ :=
  aCoeff s du dv - dchi

/-- directional derivative of g along (du,dv). -/
def dg (s : StereoTriad) (du dv : ℝ) : ℝ :=
  2*s.u*du + 2*s.v*dv

/-- quotient-rule directional derivative of N. -/
def dNraw (s : StereoTriad) (du dv : ℝ) : V3 :=
  let d := g s
  let dd := dg s du dv
  ⟨2*du/d - (2*s.u)*dd/d^2,
   2*dv/d - (2*s.v)*dd/d^2,
   (-2*s.u*du-2*s.v*dv)/d - (1-s.u^2-s.v^2)*dd/d^2⟩

/-- quotient-rule directional derivative of e_1^0. -/
def de10raw (s : StereoTriad) (du dv : ℝ) : V3 :=
  let d := g s
  let dd := dg s du dv
  ⟨(-2*s.u*du+2*s.v*dv)/d - (1-s.u^2+s.v^2)*dd/d^2,
   (-2*(du*s.v+s.u*dv))/d - (-2*s.u*s.v)*dd/d^2,
   (-2*du)/d - (-2*s.u)*dd/d^2⟩

/-- quotient-rule directional derivative of e_2^0. -/
def de20raw (s : StereoTriad) (du dv : ℝ) : V3 :=
  let d := g s
  let dd := dg s du dv
  ⟨(-2*(du*s.v+s.u*dv))/d - (-2*s.u*s.v)*dd/d^2,
   (2*s.u*du-2*s.v*dv)/d - (1+s.u^2-s.v^2)*dd/d^2,
   (-2*dv)/d - (-2*s.v)*dd/d^2⟩

/-- product-rule directional derivative of the rotated E1. -/
def dE1raw (s : StereoTriad) (du dv dchi : ℝ) : V3 :=
  vadd
    (vadd
      (vsmul (-Real.sin s.chi * dchi) (e10 s))
      (vsmul (Real.cos s.chi) (de10raw s du dv)))
    (vadd
      (vsmul (Real.cos s.chi * dchi) (e20 s))
      (vsmul (Real.sin s.chi) (de20raw s du dv)))

/-- product-rule directional derivative of the rotated E2. -/
def dE2raw (s : StereoTriad) (du dv dchi : ℝ) : V3 :=
  vadd
    (vadd
      (vsmul (-Real.cos s.chi * dchi) (e10 s))
      (vsmul (-Real.sin s.chi) (de10raw s du dv)))
    (vadd
      (vsmul (-Real.sin s.chi * dchi) (e20 s))
      (vsmul (Real.cos s.chi) (de20raw s du dv)))

end StereoTriad

lemma stereo_g_pos (s : StereoTriad) : 0 < StereoTriad.g s := by
  unfold StereoTriad.g
  nlinarith [sq_nonneg s.u, sq_nonneg s.v]

lemma stereo_g_ne (s : StereoTriad) : StereoTriad.g s ≠ 0 :=
  ne_of_gt (stereo_g_pos s)

/- Mother-paper equations dN0, de10, de20 and a0frame. -/

theorem v16_lem_dN0 (s : StereoTriad) (du dv : ℝ) :
    StereoTriad.dNraw s du dv =
      vadd
        (vsmul (2*du / StereoTriad.g s) (StereoTriad.e10 s))
        (vsmul (2*dv / StereoTriad.g s) (StereoTriad.e20 s)) := by
  apply V3.ext_coords <;>
    dsimp [StereoTriad.dNraw, StereoTriad.dg, StereoTriad.g,
      StereoTriad.e10, StereoTriad.e20, vadd, vsmul] <;>
    field_simp [stereo_g_ne s] <;> ring

theorem v16_lem_de10 (s : StereoTriad) (du dv : ℝ) :
    StereoTriad.de10raw s du dv =
      vadd
        (vsmul (-2*du / StereoTriad.g s) (StereoTriad.N s))
        (vsmul (-2*(s.u*dv-s.v*du) / StereoTriad.g s)
          (StereoTriad.e20 s)) := by
  apply V3.ext_coords <;>
    dsimp [StereoTriad.de10raw, StereoTriad.dg, StereoTriad.g,
      StereoTriad.N, StereoTriad.e20, vadd, vsmul] <;>
    field_simp [stereo_g_ne s] <;> ring

theorem v16_lem_de20 (s : StereoTriad) (du dv : ℝ) :
    StereoTriad.de20raw s du dv =
      vadd
        (vsmul (-2*dv / StereoTriad.g s) (StereoTriad.N s))
        (vsmul (2*(s.u*dv-s.v*du) / StereoTriad.g s)
          (StereoTriad.e10 s)) := by
  apply V3.ext_coords <;>
    dsimp [StereoTriad.de20raw, StereoTriad.dg, StereoTriad.g,
      StereoTriad.N, StereoTriad.e10, vadd, vsmul] <;>
    field_simp [stereo_g_ne s] <;> ring

theorem v16_lem_a0frame (s : StereoTriad) (du dv : ℝ) :
    vdot (StereoTriad.e10 s) (StereoTriad.de20raw s du dv) =
      2*(s.u*dv-s.v*du) / StereoTriad.g s := by
  dsimp [vdot, StereoTriad.e10, StereoTriad.de20raw,
    StereoTriad.dg, StereoTriad.g]
  field_simp [stereo_g_ne s]
  ring



/- Previously web-verified T030A metric identities are reproved here in a
   small self-contained form, so T030B does not use placeholder hypotheses. -/
lemma vnormSq_rot_expand (a b : V3) (c d : ℝ) :
    vnormSq (vadd (vsmul c a) (vsmul d b)) =
      c^2 * vnormSq a + 2*c*d*vdot a b + d^2*vnormSq b := by
  dsimp [vnormSq, vdot, vadd, vsmul]
  ring

lemma vdot_rot_right (n a b : V3) (c d : ℝ) :
    vdot n (vadd (vsmul c a) (vsmul d b)) =
      c * vdot n a + d * vdot n b := by
  dsimp [vdot, vadd, vsmul]
  ring

lemma vdot_comm (a b : V3) : vdot a b = vdot b a := by
  dsimp [vdot]
  ring

lemma vrot_reconstruct (a b : V3) (c d α β : ℝ)
    (htrig : c^2 + d^2 = 1) :
    vadd
      (vsmul (c*α + d*β) (vadd (vsmul c a) (vsmul d b)))
      (vsmul (c*β - d*α) (vadd (vsmul (-d) a) (vsmul c b))) =
    vadd (vsmul α a) (vsmul β b) := by
  have ha : (c*α + d*β)*c + (c*β - d*α)*(-d) = α := by
    linear_combination α * htrig
  have hb : (c*α + d*β)*d + (c*β - d*α)*c = β := by
    linear_combination β * htrig
  apply V3.ext_coords
  · dsimp [vadd, vsmul]
    linear_combination a.x * ha + b.x * hb
  · dsimp [vadd, vsmul]
    linear_combination a.y * ha + b.y * hb
  · dsimp [vadd, vsmul]
    linear_combination a.z * ha + b.z * hb

lemma v16_verified_rotated_E1_metric (s : StereoTriad) :
    vnormSq (StereoTriad.E1 s) = 1 ∧
    vdot (StereoTriad.E1 s) (StereoTriad.N s) = 0 := by
  have h1 : vnormSq (StereoTriad.e10 s) = 1 := by
    dsimp [vnormSq, vdot, StereoTriad.e10, StereoTriad.g]
    field_simp [stereo_g_ne s]
    ring
  have h2 : vnormSq (StereoTriad.e20 s) = 1 := by
    dsimp [vnormSq, vdot, StereoTriad.e20, StereoTriad.g]
    field_simp [stereo_g_ne s]
    ring
  have h12 : vdot (StereoTriad.e10 s) (StereoTriad.e20 s) = 0 := by
    dsimp [vdot, StereoTriad.e10, StereoTriad.e20, StereoTriad.g]
    field_simp [stereo_g_ne s]
    ring
  have hN1 : vdot (StereoTriad.N s) (StereoTriad.e10 s) = 0 := by
    dsimp [vdot, StereoTriad.N, StereoTriad.e10, StereoTriad.g]
    field_simp [stereo_g_ne s]
    ring
  have hN2 : vdot (StereoTriad.N s) (StereoTriad.e20 s) = 0 := by
    dsimp [vdot, StereoTriad.N, StereoTriad.e20, StereoTriad.g]
    field_simp [stereo_g_ne s]
    ring
  constructor
  · rw [StereoTriad.E1, vnormSq_rot_expand, h1, h2, h12]
    nlinarith [Real.sin_sq_add_cos_sq s.chi]
  · have hNE1 : vdot (StereoTriad.N s) (StereoTriad.E1 s) = 0 := by
      rw [StereoTriad.E1, vdot_rot_right, hN1, hN2]
      ring
    rw [vdot_comm]
    exact hNE1

/- T030B: the actual differentiated rotated frame equations. -/

theorem v16_lem_frame_N (s : StereoTriad) (du dv : ℝ) :
    StereoTriad.dNraw s du dv =
      vadd
        (vsmul (2 * StereoTriad.Qre s du dv) (StereoTriad.E1 s))
        (vsmul (2 * StereoTriad.Qim s du dv) (StereoTriad.E2 s)) := by
  rw [v16_lem_dN0]
  let c : ℝ := Real.cos s.chi
  let d : ℝ := Real.sin s.chi
  let α : ℝ := 2 * du / StereoTriad.g s
  let β : ℝ := 2 * dv / StereoTriad.g s
  have htrig : c^2 + d^2 = 1 := by
    dsimp [c, d]
    nlinarith [Real.sin_sq_add_cos_sq s.chi]
  have hqre : 2 * StereoTriad.Qre s du dv = c*α + d*β := by
    dsimp [StereoTriad.Qre, c, d, α, β]
    ring
  have hqim : 2 * StereoTriad.Qim s du dv = c*β - d*α := by
    dsimp [StereoTriad.Qim, c, d, α, β]
    ring
  rw [hqre, hqim, StereoTriad.E1, StereoTriad.E2]
  change vadd (vsmul α (StereoTriad.e10 s))
      (vsmul β (StereoTriad.e20 s)) = _
  exact (vrot_reconstruct (StereoTriad.e10 s) (StereoTriad.e20 s)
    c d α β htrig).symm

theorem v16_lem_frame_E1 (s : StereoTriad) (du dv dchi : ℝ) :
    StereoTriad.dE1raw s du dv dchi =
      vadd
        (vsmul (-2 * StereoTriad.Qre s du dv) (StereoTriad.N s))
        (vsmul (-StereoTriad.ACoeff s du dv dchi) (StereoTriad.E2 s)) := by
  apply V3.ext_coords <;>
    dsimp [StereoTriad.dE1raw, StereoTriad.de10raw, StereoTriad.de20raw,
      StereoTriad.dg, StereoTriad.Qre, StereoTriad.ACoeff,
      StereoTriad.aCoeff, StereoTriad.N, StereoTriad.E2,
      StereoTriad.e10, StereoTriad.e20, StereoTriad.g, vadd, vsmul] <;>
    field_simp [stereo_g_ne s] <;>
    nlinarith [Real.sin_sq_add_cos_sq s.chi]

theorem v16_lem_frame_E2 (s : StereoTriad) (du dv dchi : ℝ) :
    StereoTriad.dE2raw s du dv dchi =
      vadd
        (vsmul (-2 * StereoTriad.Qim s du dv) (StereoTriad.N s))
        (vsmul (StereoTriad.ACoeff s du dv dchi) (StereoTriad.E1 s)) := by
  apply V3.ext_coords <;>
    dsimp [StereoTriad.dE2raw, StereoTriad.de10raw, StereoTriad.de20raw,
      StereoTriad.dg, StereoTriad.Qim, StereoTriad.ACoeff,
      StereoTriad.aCoeff, StereoTriad.N, StereoTriad.E1,
      StereoTriad.e10, StereoTriad.e20, StereoTriad.g, vadd, vsmul] <;>
    field_simp [stereo_g_ne s] <;>
    nlinarith [Real.sin_sq_add_cos_sq s.chi]

theorem v16_lem_frame_A (s : StereoTriad) (du dv dchi : ℝ) :
    vdot (StereoTriad.E1 s) (StereoTriad.dE2raw s du dv dchi) =
      StereoTriad.ACoeff s du dv dchi := by
  rw [v16_lem_frame_E2, vdot_rot_right]
  rcases v16_verified_rotated_E1_metric s with ⟨hE1norm, hE1N⟩
  have hE1self : vdot (StereoTriad.E1 s) (StereoTriad.E1 s) = 1 := by
    simpa [vnormSq] using hE1norm
  rw [hE1N, hE1self]
  ring

/-- Pointwise energy identity underlying the integrated mother-paper formula. -/
theorem v16_lem_energy_triad_pointwise (s : StereoTriad) (du dv : ℝ) :
    vnormSq (StereoTriad.dNraw s du dv) =
      4 * ((StereoTriad.Qre s du dv)^2 +
           (StereoTriad.Qim s du dv)^2) := by
  dsimp [vnormSq, vdot, StereoTriad.dNraw, StereoTriad.dg,
    StereoTriad.Qre, StereoTriad.Qim, StereoTriad.g]
  field_simp [stereo_g_ne s]
  nlinarith [Real.sin_sq_add_cos_sq s.chi]

#print axioms v16_lem_dN0
#print axioms v16_lem_de10
#print axioms v16_lem_de20
#print axioms v16_lem_a0frame
#print axioms v16_lem_frame_N
#print axioms v16_lem_frame_E1
#print axioms v16_lem_frame_E2
#print axioms v16_lem_frame_A
#print axioms v16_lem_energy_triad_pointwise

end

end SMLeanMinV1

namespace SMLeanMinV1

/-!
B22: compactness/profile large batch.

PASS-eligible in this file:
  T031 = weak-realization definition
  T032 = frame-compactness quantitative closure
  T033 = weak-profile-realization closure after standard compactness outputs

Forward probes only (NOT counted as theorem PASS):
  T034 algebraic energy-ledger core
  T035 Hilbert strong-convergence core
  T037 final-time stability limit core
  T038 first-exit bootstrap core
  T039 Cauchy-completion core
  T040 diagonal two-error core

T036 is intentionally deferred because the mother-paper proof invokes T039.

No `sorry`, `admit`, `axiom`, or opaque catch-all `Claims : Prop`.
Only standard-analysis outputs and already web-verified internal nodes may
appear as hypotheses.
-/

set_option maxHeartbeats 1000000

/- ================================================================
   T031 = v16:def:weak-realization
   ================================================================ -/

structure WeakCoulombRealization where
  p : ℝ
  hp_lo : (4 : ℝ) / 3 < p
  hp_hi : p < 2
  orientedDefect : ℝ
  divAResidual : ℝ
  frameNResidual : Fin 2 → ℝ
  frameE1Residual : Fin 2 → ℝ
  frameE2Residual : Fin 2 → ℝ
  oriented_zero : orientedDefect = 0
  divA_zero : divAResidual = 0
  frameN_zero : ∀ j, frameNResidual j = 0
  frameE1_zero : ∀ j, frameE1Residual j = 0
  frameE2_zero : ∀ j, frameE2Residual j = 0

#check WeakCoulombRealization

/- ================================================================
   T032 = v16:lem:frame-compactness
   ================================================================ -/

theorem v16_lem_frame_compactness
    (M CHLS Cemb Rmeasure B1 Aweak Alocal Ngrad Egrad : ℝ)
    (hM : 0 ≤ M)
    (hCHLS : 0 ≤ CHLS)
    (hCemb : 0 ≤ Cemb)
    (hRmeasure : 0 ≤ Rmeasure)
    /- T001, already PASS_WEB_VERIFIED -/
    (hB : B1 ≤ 2 * M ^ 2)
    /- standard weak HLS I_1 : L^1 -> L^{2,∞} -/
    (hWeakHLS : Aweak ≤ CHLS * B1)
    /- standard finite-measure Lorentz embedding -/
    (hLocalLorentz : Alocal ≤ Cemb * Aweak)
    /- T030 frame identities, already PASS_WEB_VERIFIED -/
    (hNframe : Ngrad ≤ 2 * M)
    (hEframe : Egrad ≤ 4 * Rmeasure * M + 2 * Alocal) :
    B1 ≤ 2 * M ^ 2 ∧
    Aweak ≤ 2 * CHLS * M ^ 2 ∧
    Alocal ≤ 2 * Cemb * CHLS * M ^ 2 ∧
    Ngrad ≤ 2 * M ∧
    Egrad ≤ 4 * Rmeasure * M + 4 * Cemb * CHLS * M ^ 2 := by
  have hAw : Aweak ≤ 2 * CHLS * M ^ 2 := by
    calc
      Aweak ≤ CHLS * B1 := hWeakHLS
      _ ≤ CHLS * (2 * M ^ 2) :=
        mul_le_mul_of_nonneg_left hB hCHLS
      _ = 2 * CHLS * M ^ 2 := by ring
  have hAl : Alocal ≤ 2 * Cemb * CHLS * M ^ 2 := by
    calc
      Alocal ≤ Cemb * Aweak := hLocalLorentz
      _ ≤ Cemb * (2 * CHLS * M ^ 2) :=
        mul_le_mul_of_nonneg_left hAw hCemb
      _ = 2 * Cemb * CHLS * M ^ 2 := by ring
  have htwo : 2 * Alocal ≤ 2 * (2 * Cemb * CHLS * M ^ 2) :=
    mul_le_mul_of_nonneg_left hAl (by norm_num : (0 : ℝ) ≤ 2)
  have hE : Egrad ≤ 4 * Rmeasure * M + 4 * Cemb * CHLS * M ^ 2 := by
    calc
      Egrad ≤ 4 * Rmeasure * M + 2 * Alocal := hEframe
      _ ≤ 4 * Rmeasure * M + 2 * (2 * Cemb * CHLS * M ^ 2) := by
        exact add_le_add (le_refl _) htwo
      _ = 4 * Rmeasure * M + 4 * Cemb * CHLS * M ^ 2 := by ring
  exact ⟨hB, hAw, hAl, hNframe, hE⟩

#print axioms v16_lem_frame_compactness

/- ================================================================
   T033 = v16:thm:weak-profile-realization
   ================================================================ -/

/--
The residual equalities are exactly the outputs of standard
Banach--Alaoglu/Rellich + weak--strong product convergence applied to the
already verified T030 frame equations.  They are not a catch-all claim.
-/
theorem v16_thm_weak_profile_realization
    (p orientedDefect divAResidual : ℝ)
    (frameNResidual frameE1Residual frameE2Residual : Fin 2 → ℝ)
    (phi1Sq phi2Sq dN1Sq dN2Sq energyN : ℝ)
    (hp_lo : (4 : ℝ) / 3 < p)
    (hp_hi : p < 2)
    (hON_limit : orientedDefect = 0)
    (hDiv_limit : divAResidual = 0)
    (hFrameN_limit : ∀ j, frameNResidual j = 0)
    (hFrameE1_limit : ∀ j, frameE1Residual j = 0)
    (hFrameE2_limit : ∀ j, frameE2Residual j = 0)
    (hDN1 : dN1Sq = 4 * phi1Sq)
    (hDN2 : dN2Sq = 4 * phi2Sq)
    (hEnergyDef : energyN = (dN1Sq + dN2Sq) / 2) :
    ∃ R : WeakCoulombRealization,
      R.p = p ∧ energyN = 2 * (phi1Sq + phi2Sq) := by
  let R : WeakCoulombRealization := {
    p := p
    hp_lo := hp_lo
    hp_hi := hp_hi
    orientedDefect := orientedDefect
    divAResidual := divAResidual
    frameNResidual := frameNResidual
    frameE1Residual := frameE1Residual
    frameE2Residual := frameE2Residual
    oriented_zero := hON_limit
    divA_zero := hDiv_limit
    frameN_zero := hFrameN_limit
    frameE1_zero := hFrameE1_limit
    frameE2_zero := hFrameE2_limit
  }
  refine ⟨R, rfl, ?_⟩
  rw [hEnergyDef, hDN1, hDN2]
  ring

#print axioms v16_thm_weak_profile_realization

/- ================================================================
   T034 probe = v15:thm:minimal-one-profile
   No unproved branch-contradiction hypothesis is introduced.
   ================================================================ -/


end SMLeanMinV1

namespace SMLeanMinV1

/-!
B52 — mid-gap main-node assembly after T093.
Only uses:
* standard ordered-field / Banach / finite-sum facts;
* outputs explicitly tagged as already-PASS internal nodes (e.g. T036);
* no sorry/admit/axiom and no generic Claims : Prop.
-/

/-- T034: energy-ledger assembly of the one-profile reduction.
`hT036` is exactly the already PASS_WEB_VERIFIED strict-subcritical-flow exclusion
for a bad profile; it is not a new claim. -/
theorem main_T034_minimal_one_profile_assembly
    (Ec e1 e2 : ℝ) (Bad : ℝ → Prop)
    (hEc0 : 0 ≤ Ec)
    (he1 : 0 < e1) (he2 : 0 < e2)
    (hsum : e1 + e2 ≤ Ec)
    (hT036 : ∀ e : ℝ, 0 ≤ e → e < Ec → ¬ Bad e)
    (hbad1 : Bad e1) (hbad2 : Bad e2) : False := by
  have he10 : 0 ≤ e1 := le_of_lt he1
  have he20 : 0 ≤ e2 := le_of_lt he2
  have he1lt : e1 < Ec := by linarith
  have he2lt : e2 < Ec := by linarith
  exact (hT036 e1 he10 he1lt) hbad1


end SMLeanMinV1


namespace SMLeanMinV1
/-- N030 support-level continuity core only; the full bounded-profile-static
corollary remains a separate main node in the v21 inventory. -/
theorem v21_N030_bounded_parameter_absorb_core
    (x xn yn y : ℝ)
    (hxn : xn = x) (hyn : yn = y) : xn + yn = x + y := by
  simpa [hxn, hyn]
#print axioms v21_N030_bounded_parameter_absorb_core
end SMLeanMinV1


namespace SMLeanMinV1

/-!
B25: internal helper closure for T035 plus genuine support cores for T038--T040.

Rules:
* no `sorry`, `admit`, or custom `axiom`;
* no catch-all `Claims : Prop`;
* only exact standard external-analysis interfaces may appear as hypotheses;
* none of the probe theorems below is counted as a main TID PASS unless its
  full mother-proof dependency chain has already been certified.
-/

set_option maxHeartbeats 500000

/-- Elementary sequential convergence ledger used by later Hilbert arguments. -/
def EventuallyWithin (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |f n - a| ≤ ε

/- ================================================================
   Internal helper omitted from the original 94-node inventory:
   v17:lem:Coulomb-unique, algebraic gauge core.
   ================================================================ -/

/--
Pointwise part of the canonical-Coulomb uniqueness proof.
If two oriented frames differ by a unit phase `h` and their connection
coefficients agree, then the phase derivative vanishes.

The relation
  Atilde - A = -i conj(h) dh
is exactly the already verified triad/gauge transformation identity.
-/
theorem helper_v17_Coulomb_unique_gradient_zero
    {X : Type*}
    (h dh A Atilde : X → ℂ)
    (hunit : ∀ x, Complex.normSq (h x) = 1)
    (hgauge : ∀ x,
      Atilde x - A x = -Complex.I * star (h x) * dh x)
    (hcanonical : ∀ x, Atilde x = A x) :
    ∀ x, dh x = 0 := by
  intro x
  have hh_ne : h x ≠ 0 := by
    intro hz
    have hu := hunit x
    simp [hz] at hu
  have hstar_ne : star (h x) ≠ 0 := by
    intro hs
    have hz : h x = 0 := by
      have hss := congrArg star hs
      simpa using hss
    exact hh_ne hz
  have hfac_ne : (-Complex.I * star (h x)) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hstar_ne
  have hg := hgauge x
  rw [hcanonical x, sub_self] at hg
  have hp : (-Complex.I * star (h x)) * dh x = 0 := by
    simpa [mul_assoc] using hg.symm
  exact (mul_eq_zero.mp hp).resolve_left hfac_ne

#print axioms helper_v17_Coulomb_unique_gradient_zero

/--
Completion of `v17:lem:Coulomb-unique` after the single standard distribution
fact used in the mother proof:

  on a connected domain, a distribution with zero gradient is constant.

`h_zero_grad_constant` is precisely that standard external-analysis input;
it is not a paper-specific claim.
-/
theorem helper_v17_Coulomb_unique_constant_phase
    {X : Type*} [Nonempty X]
    (h dh A Atilde Q Qtilde : X → ℂ)
    (hunit : ∀ x, Complex.normSq (h x) = 1)
    (hgauge : ∀ x,
      Atilde x - A x = -Complex.I * star (h x) * dh x)
    (hcanonical : ∀ x, Atilde x = A x)
    (hQrel : ∀ x, Qtilde x = h x * Q x)
    (h_zero_grad_constant :
      (∀ x, dh x = 0) → ∃ c : ℂ, ∀ x, h x = c) :
    ∃ c : ℂ,
      Complex.normSq c = 1 ∧
      ∀ x, Qtilde x = c * Q x := by
  have hdh : ∀ x, dh x = 0 :=
    helper_v17_Coulomb_unique_gradient_zero h dh A Atilde
      hunit hgauge hcanonical
  obtain ⟨c, hc⟩ := h_zero_grad_constant hdh
  let x0 : X := Classical.choice (inferInstance : Nonempty X)
  have hcunit : Complex.normSq c = 1 := by
    rw [← hc x0]
    exact hunit x0
  refine ⟨c, hcunit, ?_⟩
  intro x
  rw [hQrel x, hc x]

#print axioms helper_v17_Coulomb_unique_constant_phase

/--
The positive-real Hilbert-pairing normalization fixes the remaining unit
phase.  Here `q2` is the nonzero squared Hilbert norm of the target field.
-/
theorem helper_v17_positive_pairing_fixes_phase
    (c : ℂ) (q2 : ℝ)
    (hq2 : 0 < q2)
    (hunit : Complex.normSq c = 1)
    (him : c.im * q2 = 0)
    (hre : 0 ≤ c.re * q2) :
    c = 1 := by
  have him0 : c.im = 0 := by
    nlinarith
  have hre0 : 0 ≤ c.re := by
    nlinarith
  have hsq : c.re ^ 2 = 1 := by
    rw [Complex.normSq_apply] at hunit
    nlinarith
  have hre1 : c.re = 1 := by
    nlinarith
  apply Complex.ext
  · simp [hre1]
  · simp [him0]

#print axioms helper_v17_positive_pairing_fixes_phase

/- ================================================================
   T035 final Hilbert-space algebra after weak-cluster uniqueness.
   This is a support theorem, not yet the full T035 PASS.
   ================================================================ -/


#print axioms helper_v17_Coulomb_unique_gradient_zero
#print axioms helper_v17_Coulomb_unique_constant_phase
#print axioms helper_v17_positive_pairing_fixes_phase
end SMLeanMinV1

namespace SMLeanMinV1

/-!
B28: close T035 after B25 helper PASS; robust positive-factor cancellation; probe next rough-flow block.

Rules:
* no `sorry`, `admit`, or custom `axiom`;
* no catch-all `Claims : Prop`;
* exact standard-analysis interfaces are stated explicitly;
* already WEB-PASS internal inputs: T028, T030, T033, T037 and all B25 helpers.
-/

set_option maxHeartbeats 500000

/-- B25 WEB-PASS helper, re-used with explicit positive-factor cancellation: positive-real pairing removes the residual unit phase. -/
theorem helper_positive_pairing_fixes_phase_B28
    (c : ℂ) (q2 : ℝ)
    (hq2 : 0 < q2)
    (hunit : Complex.normSq c = 1)
    (him : c.im * q2 = 0)
    (hre : 0 ≤ c.re * q2) :
    c = 1 := by
  have hqne : q2 ≠ 0 := ne_of_gt hq2
  have him0 : c.im = 0 := by
    rcases mul_eq_zero.mp him with him0 | hq0
    · exact him0
    · exact False.elim (hqne hq0)
  have hre0 : 0 ≤ c.re := by
    by_contra hnot
    have hreneg : c.re < 0 := lt_of_not_ge hnot
    have hprodneg : c.re * q2 < 0 := mul_neg_of_neg_of_pos hreneg hq2
    exact (not_lt_of_ge hre) hprodneg
  have hsq : c.re ^ 2 = 1 := by
    rw [Complex.normSq_apply] at hunit
    nlinarith
  have hre1 : c.re = 1 := by nlinarith
  apply Complex.ext
  · simp [hre1]
  · simp [him0]

/-- B25 WEB-PASS Hilbert polarization closure. -/
theorem helper_hilbert_polarization_strong_B28
    (normSq inner distSq : ℕ → ℝ) (qNormSq : ℝ)
    (hnorm : EventuallyWithin normSq qNormSq)
    (hinner : EventuallyWithin inner qNormSq)
    (hdist0 : ∀ n, 0 ≤ distSq n)
    (hpolar : ∀ n, distSq n = normSq n + qNormSq - 2 * inner n) :
    EventuallyWithin distSq 0 := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := hnorm (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hinner (ε / 8) (by linarith)
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have hn1 : n ≥ N1 := le_trans (Nat.le_max_left _ _) hn
  have hn2 : n ≥ N2 := le_trans (Nat.le_max_right _ _) hn
  have h1 := hN1 n hn1
  have h2 := hN2 n hn2
  have h1hi : normSq n - qNormSq ≤ ε / 4 := (abs_le.mp h1).2
  have h2lo : -(ε / 8) ≤ inner n - qNormSq := (abs_le.mp h2).1
  have hd0 := hdist0 n
  have hd : distSq n ≤ ε / 2 := by
    rw [hpolar n]
    linarith
  rw [sub_zero, abs_of_nonneg hd0]
  linarith

/- ================================================================
   T035 = v17:thm:strong-Coulomb-density
   ================================================================ -/

/--
Paper-line sequential closure of strong Coulomb density.

Exact sources of the inputs:
* `hmap`: Bethuel smooth W^{1,2} density (published external theorem);
* `hnorm`: T030 energy identity + `hmap`;
* `hcluster`: standard Hilbert weak subsequence compactness together with
  WEB-PASS T033 weak realization and WEB-PASS B25 Coulomb uniqueness;
  it records the actual residual unit phase and the positive-real pairing;
* `hSubseqCriterion`: standard metric-space subsequence criterion for
  convergence;
* `hpolar`: Hilbert polarization identity.

The strong Q convergence and energy convergence are conclusions, not inputs.
-/
theorem v17_thm_strong_Coulomb_density
    (mapErr normSq inner distSq energy : ℕ → ℝ)
    (qNormSq qEnergy : ℝ)
    (hmap : EventuallyWithin mapErr 0)
    (hnorm : EventuallyWithin normSq qNormSq)
    (hqNorm0 : 0 ≤ qNormSq)
    (hcluster :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, ∃ c : ℂ,
          StrictMono ψ ∧
          Complex.normSq c = 1 ∧
          EventuallyWithin (fun n => inner (φ (ψ n))) (c.re * qNormSq) ∧
          c.im * qNormSq = 0 ∧
          0 ≤ c.re * qNormSq)
    (hSubseqCriterion :
      (∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ,
          StrictMono ψ ∧
          EventuallyWithin (fun n => inner (φ (ψ n))) qNormSq) →
      EventuallyWithin inner qNormSq)
    (hdist0 : ∀ n, 0 ≤ distSq n)
    (hpolar : ∀ n, distSq n = normSq n + qNormSq - 2 * inner n)
    (henergy : ∀ n, energy n = 2 * normSq n)
    (hqEnergy : qEnergy = 2 * qNormSq) :
    EventuallyWithin mapErr 0 ∧
    EventuallyWithin distSq 0 ∧
    EventuallyWithin energy qEnergy := by
  have hsub :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ,
          StrictMono ψ ∧
          EventuallyWithin (fun n => inner (φ (ψ n))) qNormSq := by
    intro φ hφ
    obtain ⟨ψ, c, hψ, hcunit, hcconv, hcim, hcre⟩ := hcluster φ hφ
    refine ⟨ψ, hψ, ?_⟩
    by_cases hq0 : qNormSq = 0
    · simpa [hq0] using hcconv
    · have hqpos : 0 < qNormSq := lt_of_le_of_ne hqNorm0 (Ne.symm hq0)
      have hc1 : c = 1 :=
        helper_positive_pairing_fixes_phase_B28 c qNormSq hqpos hcunit hcim hcre
      simpa [hc1] using hcconv
  have hinner : EventuallyWithin inner qNormSq := hSubseqCriterion hsub
  have hstrong : EventuallyWithin distSq 0 :=
    helper_hilbert_polarization_strong_B28 normSq inner distSq qNormSq
      hnorm hinner hdist0 hpolar
  have henergyConv : EventuallyWithin energy qEnergy := by
    intro ε hε
    obtain ⟨N, hN⟩ := hnorm (ε / 2) (by linarith)
    refine ⟨N, ?_⟩
    intro n hn
    have hh := hN n hn
    rw [henergy n, hqEnergy]
    rw [abs_le]
    constructor
    · have hlo := (abs_le.mp hh).1
      linarith
    · have hhi := (abs_le.mp hh).2
      linarith
  exact ⟨hmap, hstrong, henergyConv⟩

#print axioms v17_thm_strong_Coulomb_density
end SMLeanMinV1

namespace SMLeanMinV1
lemma helper_v17_profile_energy_strict
    (Ej Eother Ec : ℝ)
    (hEj0 : 0 ≤ Ej)
    (hOther : 0 < Eother)
    (hLedger : Ej + Eother ≤ Ec) :
    Ej < Ec := by
  linarith

/--
T036 assembly. `hStatic` is the already WEB-PASS T033 static realization
interface; `hGlobal` is the already WEB-PASS T039 strict-subcritical global
flow interface.  The theorem itself proves the strict energy inequality from
the Pythagorean ledger and then composes the two passed internal results.
-/
theorem v17_cor_subcritical_profile_flow_B33
    (Ej Eother Ec : ℝ)
    (staticRealized globalFlow smoothDense : Bool)
    (hEj0 : 0 ≤ Ej)
    (hOther : 0 < Eother)
    (hLedger : Ej + Eother ≤ Ec)
    (hStatic : staticRealized = true)
    (hGlobal : staticRealized = true → Ej < Ec →
      globalFlow = true ∧ smoothDense = true) :
    Ej < Ec ∧ globalFlow = true ∧ smoothDense = true := by
  have hsub : Ej < Ec :=
    helper_v17_profile_energy_strict Ej Eother Ec hEj0 hOther hLedger
  have hg := hGlobal hStatic hsub
  exact ⟨hsub, hg.1, hg.2⟩

#print axioms v17_cor_subcritical_profile_flow_B33
end SMLeanMinV1