import Mathlib.Tactic

/-!
W20 full-master v19 support kernels.

This file isolates the paper-specific finite algebra/bookkeeping in the
canonical peeling argument.  The remaining analytic inputs are explicitly
registered in status/V19_EXTERNAL_SOURCE_AUDIT.md.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

/--
From the strict Gaussian test in the sharp 2D Gagliardo--Nirenberg inequality:
  pi/2 < (2/Ecar) * pi^2,
deduce Ecar < 4*pi.
-/
theorem v19_Ecar_lt_four_pi_kernel
    (Ecar : ℝ)
    (hE : 0 < Ecar)
    (hGaussian :
      Real.pi / 2 < (2 / Ecar) * Real.pi ^ 2) :
    Ecar < 4 * Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hGaussian' :
      Real.pi / 2 < (2 * Real.pi ^ 2) / Ecar := by
    calc
      Real.pi / 2 < (2 / Ecar) * Real.pi ^ 2 := hGaussian
      _ = (2 * Real.pi ^ 2) / Ecar := by ring
  have hmul :
      (Real.pi / 2) * Ecar < 2 * Real.pi ^ 2 :=
    (lt_div_iff₀ hE).mp hGaussian'
  nlinarith

/--
Fourier uniqueness for an L2 vector field that is simultaneously divergence-
free and curl-free at a nonzero frequency.
-/
theorem v19_hodge_unique_frequency_kernel
    (xi1 xi2 H1 H2 : ℝ)
    (hfreq : xi1 ^ 2 + xi2 ^ 2 ≠ 0)
    (hdiv : xi1 * H1 + xi2 * H2 = 0)
    (hcurl : -xi2 * H1 + xi1 * H2 = 0) :
    H1 = 0 ∧ H2 = 0 := by
  have h1 :
      (xi1 ^ 2 + xi2 ^ 2) * H1 = 0 := by
    linear_combination xi1 * hdiv - xi2 * hcurl
  have h2 :
      (xi1 ^ 2 + xi2 ^ 2) * H2 = 0 := by
    linear_combination xi2 * hdiv + xi1 * hcurl
  constructor
  · exact (mul_eq_zero.mp h1).resolve_left hfreq
  · exact (mul_eq_zero.mp h2).resolve_left hfreq

/--
Hodge re-gauge estimate: the orthogonal projection has norm <= 1, so any
transported-frame connection error bound transfers directly to the phase
gradient.
-/
theorem v19_regauge_projection_kernel
    (thetaGrad deltaA C amp qNorm daNorm : ℝ)
    (hProj : thetaGrad ≤ deltaA)
    (hDelta :
      deltaA ≤ C * amp * (qNorm + daNorm)) :
    thetaGrad ≤ C * amp * (qNorm + daNorm) :=
  le_trans hProj hDelta

/--
Scalar core of the unit-modulus Poincare normalization added in LeanSync v2.
If meanSq + variance = 1 and variance is small/nonnegative, then the squared
modulus of the mean is close to one.
-/
theorem v19_unit_mean_variance_kernel
    (meanSq variance eps : ℝ)
    (hvar0 : 0 ≤ variance)
    (hid : meanSq + variance = 1)
    (hsmall : variance ≤ eps) :
    1 - eps ≤ meanSq ∧ meanSq ≤ 1 := by
  constructor <;> linarith

/--
Finite peeling error accumulation.  If J>0 and the total error is bounded by
J copies of eta/J, then it is bounded by eta.
-/
theorem v19_finite_peel_error_kernel
    (J eta totalErr : ℝ)
    (hJ : 0 < J)
    (hErr : totalErr ≤ J * (eta / J)) :
    totalErr ≤ eta := by
  have hJne : J ≠ 0 := ne_of_gt hJ
  have hEq : J * (eta / J) = eta := by
    field_simp [hJne]
  simpa [hEq] using hErr

/--
Unit-modulus phases do not change the L2 norm; the finite energy ledger
therefore only sees the Hilbert Pythagorean masses plus the controlled peel
error.
-/
theorem v19_energy_ledger_error_kernel
    (exactProfiles residual total err : ℝ)
    (hledger :
      total = exactProfiles + residual + err) :
    total - err = exactProfiles + residual := by
  linarith

/-- Logical assembly of the canonical GPEEL conclusion. -/
theorem v19_GPEEL_dependency
    (TimeBlock PhaseTransport FinitePeel GPEEL : Prop)
    (hTime : TimeBlock)
    (hPhase : PhaseTransport)
    (hPeel : FinitePeel)
    (hAssemble :
      TimeBlock → PhaseTransport → FinitePeel → GPEEL) :
    GPEEL :=
  hAssemble hTime hPhase hPeel

#print axioms v19_Ecar_lt_four_pi_kernel
#print axioms v19_hodge_unique_frequency_kernel
#print axioms v19_regauge_projection_kernel
#print axioms v19_unit_mean_variance_kernel
#print axioms v19_finite_peel_error_kernel
#print axioms v19_energy_ledger_error_kernel
#print axioms v19_GPEEL_dependency

end SMScattering.W20Full
