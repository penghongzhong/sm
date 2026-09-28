import Mathlib.Tactic

/-!
Section 2 finite-algebra kernel for the stereographic curvature identity.

Let z = u + i v,
  g = 1 + u^2 + v^2,
  n_j = u v_j - v u_j,
  a_j = 2 n_j / g.
After the ordinary quotient rule and commutation of the mixed derivatives
u_12=u_21, v_12=v_21, the paper line
  ∂₁ a₂ - ∂₂ a₁ = 4 g⁻² (u₁ v₂ - v₁ u₂)
reduces exactly to the identity proved below.

No sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

theorem stereographic_curvature_algebra
    (u v u1 v1 u2 v2 u12 v12 : ℝ)
    (g g1 g2 n1 n2 d1n2 d2n1 : ℝ)
    (hg : g = 1 + u^2 + v^2)
    (hg_ne : g ≠ 0)
    (hg1 : g1 = 2*u*u1 + 2*v*v1)
    (hg2 : g2 = 2*u*u2 + 2*v*v2)
    (hn1 : n1 = u*v1 - v*u1)
    (hn2 : n2 = u*v2 - v*u2)
    (hd1 :
      d1n2 = u1*v2 + u*v12 - v1*u2 - v*u12)
    (hd2 :
      d2n1 = u2*v1 + u*v12 - v2*u1 - v*u12) :
    2 * (d1n2 * g - n2 * g1) / g^2
      - 2 * (d2n1 * g - n1 * g2) / g^2
      =
    4 * (u1*v2 - v1*u2) / g^2 := by
  rw [hg1, hg2, hn1, hn2, hd1, hd2]
  field_simp [hg_ne]
  rw [hg]
  ring

#print axioms stereographic_curvature_algebra

end SMScattering.Section2
