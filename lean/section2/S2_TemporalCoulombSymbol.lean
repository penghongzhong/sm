import Mathlib.Tactic

/-!
Section 2: Fourier-symbol algebra for the temporal Coulomb coefficient.

For r2 = xi1^2+xi2^2, the divergence identity
  div F = 4 xi_j xi_l S_jl - 2 r2 m
and -Delta A0 = div F imply
  A0hat = 4 (xi_j xi_l/r2) S_jl - 2 m.

No sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

theorem temporal_coulomb_symbol
    (r2 quadS mass A0 divF : ℝ)
    (hr : r2 ≠ 0)
    (hdiv : divF = 4 * quadS - 2 * r2 * mass)
    (hpoisson : r2 * A0 = divF) :
    A0 = 4 * (quadS / r2) - 2 * mass := by
  rw [hdiv] at hpoisson
  apply (eq_div_iff hr).2
  calc
    A0 * r2 = r2 * A0 := by ring
    _ = 4 * quadS - 2 * r2 * mass := hpoisson
    _ = (4 * (quadS / r2) - 2 * mass) * r2 := by
      field_simp [hr]
      ring

#print axioms temporal_coulomb_symbol

end SMScattering.Section2
