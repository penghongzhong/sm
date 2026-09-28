import Mathlib.Tactic

/-!
Section 2 stereographic-curvature jet algebra.

For z = u + i v and
  a_j = 2 (u v_j - v u_j) / (1 + u^2 + v^2),
this file verifies the complete quotient-rule algebra for
  ∂₁ a₂ - ∂₂ a₁
at the two-jet level.  The same mixed second derivatives u₁₂,v₁₂ occur in
both directions, encoding equality of mixed derivatives for a smooth chart.

No sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

def stereoG (u v : ℝ) : ℝ :=
  1 + u^2 + v^2

def stereoN (u v uj vj : ℝ) : ℝ :=
  u * vj - v * uj

def dStereoG (u v uj vj : ℝ) : ℝ :=
  2 * u * uj + 2 * v * vj

def d1StereoN2
    (u v u1 v1 u2 v2 u12 v12 : ℝ) : ℝ :=
  u1 * v2 + u * v12 - v1 * u2 - v * u12

def d2StereoN1
    (u v u1 v1 u2 v2 u12 v12 : ℝ) : ℝ :=
  u2 * v1 + u * v12 - v2 * u1 - v * u12

/-- Exact polynomial numerator cancellation behind the curvature identity. -/
theorem stereographic_curvature_numerator
    (u v u1 v1 u2 v2 u12 v12 : ℝ) :
    2 * (
      (d1StereoN2 u v u1 v1 u2 v2 u12 v12 * stereoG u v
        - stereoN u v u2 v2 * dStereoG u v u1 v1)
      -
      (d2StereoN1 u v u1 v1 u2 v2 u12 v12 * stereoG u v
        - stereoN u v u1 v1 * dStereoG u v u2 v2)
    )
    =
    4 * (u1 * v2 - u2 * v1) := by
  simp [d1StereoN2, d2StereoN1, stereoG, stereoN, dStereoG]
  ring

/--
Full quotient-rule form:
∂₁ a₂ - ∂₂ a₁ = 4 (u₁ v₂ - u₂ v₁) / g².
-/
theorem stereographic_curvature_quotient
    (u v u1 v1 u2 v2 u12 v12 : ℝ) :
    let g := stereoG u v
    let d1a2 :=
      2 * (
        d1StereoN2 u v u1 v1 u2 v2 u12 v12 * g
        - stereoN u v u2 v2 * dStereoG u v u1 v1
      ) / g^2
    let d2a1 :=
      2 * (
        d2StereoN1 u v u1 v1 u2 v2 u12 v12 * g
        - stereoN u v u1 v1 * dStereoG u v u2 v2
      ) / g^2
    d1a2 - d2a1
      =
    4 * (u1 * v2 - u2 * v1) / g^2 := by
  dsimp
  have hgpos : 0 < stereoG u v := by
    simp [stereoG]
    nlinarith [sq_nonneg u, sq_nonneg v]
  have hg : stereoG u v ≠ 0 := ne_of_gt hgpos
  field_simp [hg]
  simp [stereoG, stereoN, dStereoG, d1StereoN2, d2StereoN1]
  ring

#print axioms stereographic_curvature_numerator
#print axioms stereographic_curvature_quotient

end SMScattering.Section2
