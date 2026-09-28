import Mathlib.Tactic

/-!
T007 / v13:prop:HHL finite algebra kernel.

This file isolates the paper-specific algebra behind the high-high-to-low
Jacobian cancellation.  All remaining estimates in the HHL proof are standard
harmonic-analysis interfaces (Littlewood--Paley, Coifman--Meyer, HLS,
Holder, Bernstein, and sequence Cauchy--Schwarz).

No sorry/admit/custom axiom.
-/

namespace SMScattering.V13

def wedge2 (a b : ℝ × ℝ) : ℝ :=
  a.1 * b.2 - a.2 * b.1

/--
The high-high Jacobian symbol may put the small output frequency on one input:
eta wedge xi = eta wedge (xi - eta).
-/
theorem jacobian_output_frequency_cancel (eta xi : ℝ × ℝ) :
    wedge2 eta xi = wedge2 eta (xi - eta) := by
  rcases eta with ⟨eta1, eta2⟩
  rcases xi with ⟨xi1, xi2⟩
  simp [wedge2]
  ring


/-- Euclidean two-dimensional Lagrange identity behind the Jacobian Cauchy bound. -/
theorem lagrange_identity_2d
    (a1 a2 b1 b2 : ℝ) :
    (a1 * b2 - a2 * b1) ^ 2 + (a1 * b1 + a2 * b2) ^ 2
      =
    (a1 ^ 2 + a2 ^ 2) * (b1 ^ 2 + b2 ^ 2) := by
  ring

/--
Abstract frequency-order form of the high-high-to-low symbol calculation.

If the second high input has size at least M/2, and the Jacobian wedge is
bounded by |eta| |xi|, then after the output Riesz factor and the two input
gradient factors the symbol is of order at most 2/M.  The displayed
cross-multiplied inequality avoids introducing square-root norms/division.
-/
theorem jacobian_symbol_order_crossmultiplied
    (M xiNorm etaNorm thetaNorm wedgeAbs : ℝ)
    (hM : 0 ≤ M)
    (hxi : 0 ≤ xiNorm)
    (heta : 0 ≤ etaNorm)
    (htheta : M / 2 ≤ thetaNorm)
    (hwedge : wedgeAbs ≤ etaNorm * xiNorm) :
    M * wedgeAbs ≤ 2 * xiNorm * etaNorm * thetaNorm := by
  have hMtheta : M ≤ 2 * thetaNorm := by
    linarith
  have hprod0 : 0 ≤ etaNorm * xiNorm := mul_nonneg heta hxi
  have h1 : M * wedgeAbs ≤ M * (etaNorm * xiNorm) :=
    mul_le_mul_of_nonneg_left hwedge hM
  have h2 :
      M * (etaNorm * xiNorm)
        ≤ (2 * thetaNorm) * (etaNorm * xiNorm) :=
    mul_le_mul_of_nonneg_right hMtheta hprod0
  calc
    M * wedgeAbs ≤ M * (etaNorm * xiNorm) := h1
    _ ≤ (2 * thetaNorm) * (etaNorm * xiNorm) := h2
    _ = 2 * xiNorm * etaNorm * thetaNorm := by ring

/--
Polarized Jacobian identity used in the two-background difference estimate.
-/
theorem jacobian_polarized_difference
    (q1 q2 p1 p2 : ℝ × ℝ) :
    wedge2 q1 q2 - wedge2 p1 p2
      =
    wedge2 (q1 - p1) q2 + wedge2 p1 (q2 - p2) := by
  rcases q1 with ⟨q11, q12⟩
  rcases q2 with ⟨q21, q22⟩
  rcases p1 with ⟨p11, p12⟩
  rcases p2 with ⟨p21, p22⟩
  simp [wedge2]
  ring

/--
The final difference weakening in v13:prop:HHL:
when 0 <= Z_* <= 1, a Z_*^2 factor may be replaced by Z_*.
-/
theorem small_square_absorb
    (Zstar R S C : ℝ)
    (hZ0 : 0 ≤ Zstar)
    (hZ1 : Zstar ≤ 1)
    (hR : 0 ≤ R)
    (hS : 0 ≤ S)
    (hC : 0 ≤ C) :
    C * Zstar ^ 2 * R * S ≤ C * Zstar * R * S := by
  have hzsq : Zstar ^ 2 ≤ Zstar := by
    nlinarith
  have hCRS : 0 ≤ C * R * S := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hzsq hCRS]

#print axioms jacobian_output_frequency_cancel
#print axioms lagrange_identity_2d
#print axioms jacobian_symbol_order_crossmultiplied
#print axioms jacobian_polarized_difference
#print axioms small_square_absorb

end SMScattering.V13
