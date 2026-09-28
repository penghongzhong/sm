import Mathlib.Tactic

/-!
Section 2 covariant product-rule algebra kernel.

This file verifies the exact cancellation of a real U(1) connection in the
Hermitian product-rule identities used in paper equation
`v12:eq:S-derivative-2`--`v12:eq:S-derivative-4`.

It does not assume the paper conclusion and contains no sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

def covDpt (A : ℝ) (dq q : ℂ) : ℂ :=
  dq - Complex.I * (A : ℂ) * q

/--
Exact cancellation of the same real connection coefficient in
conj(D q₁) q₂ + conj(q₁) D q₂.
-/
theorem covariant_pair_connection_cancel
    (A : ℝ) (q₁ q₂ dq₁ dq₂ : ℂ) :
    star (covDpt A dq₁ q₁) * q₂
      + star q₁ * covDpt A dq₂ q₂
    =
    star dq₁ * q₂ + star q₁ * dq₂ := by
  simp [covDpt]
  ring

/--
The connection contribution in conj(q) Dq is purely imaginary, hence its real
part vanishes.
-/
theorem covariant_norm_real_cancel
    (A : ℝ) (q dq : ℂ) :
    (star q * covDpt A dq q).re
      =
    (star q * dq).re := by
  simp [covDpt]
  ring

#print axioms covariant_pair_connection_cancel
#print axioms covariant_norm_real_cancel

end SMScattering.Section2
