import Mathlib.Tactic

/-!
Section 2 finite-constant kernel for paper Lemma `v12:lem:low-curv`.

Set rho = 2^m.  The multiplier derivative cost is 2*rho.
This file checks the exact coefficients 20 and 24 after the Plancherel/
multiplier and Hölder bounds have been supplied as their explicit inequalities.

No sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

theorem low_curvature_constant_20
    (rho X S₁ S₂ mass F : ℝ)
    (hrho : 0 ≤ rho)
    (hX : 0 ≤ X)
    (hS₁ : S₁ ≤ X)
    (hS₂ : S₂ ≤ X)
    (hmass : mass ≤ X)
    (hF :
      F ≤ 8 * rho * (S₁ + S₂) + 4 * rho * mass) :
    F ≤ 20 * rho * X := by
  have hsum : S₁ + S₂ ≤ 2 * X := by
    linarith
  have h8 : 0 ≤ 8 * rho := by positivity
  have h4 : 0 ≤ 4 * rho := by positivity
  have hfirst :
      8 * rho * (S₁ + S₂) ≤ 8 * rho * (2 * X) :=
    mul_le_mul_of_nonneg_left hsum h8
  have hsecond :
      4 * rho * mass ≤ 4 * rho * X :=
    mul_le_mul_of_nonneg_left hmass h4
  calc
    F ≤ 8 * rho * (S₁ + S₂) + 4 * rho * mass := hF
    _ ≤ 8 * rho * (2 * X) + 4 * rho * X := add_le_add hfirst hsecond
    _ = 20 * rho * X := by ring

theorem low_curvature_difference_constant_24
    (rho Y dS₁ dS₂ dmass dF : ℝ)
    (hrho : 0 ≤ rho)
    (hY : 0 ≤ Y)
    (hS₁ : dS₁ ≤ Y)
    (hS₂ : dS₂ ≤ Y)
    (hmass : dmass ≤ 2 * Y)
    (hF :
      dF ≤ 8 * rho * (dS₁ + dS₂) + 4 * rho * dmass) :
    dF ≤ 24 * rho * Y := by
  have hsum : dS₁ + dS₂ ≤ 2 * Y := by
    linarith
  have h8 : 0 ≤ 8 * rho := by positivity
  have h4 : 0 ≤ 4 * rho := by positivity
  have hfirst :
      8 * rho * (dS₁ + dS₂) ≤ 8 * rho * (2 * Y) :=
    mul_le_mul_of_nonneg_left hsum h8
  have hsecond :
      4 * rho * dmass ≤ 4 * rho * (2 * Y) :=
    mul_le_mul_of_nonneg_left hmass h4
  calc
    dF ≤ 8 * rho * (dS₁ + dS₂) + 4 * rho * dmass := hF
    _ ≤ 8 * rho * (2 * Y) + 4 * rho * (2 * Y) := add_le_add hfirst hsecond
    _ = 24 * rho * Y := by ring

#print axioms low_curvature_constant_20
#print axioms low_curvature_difference_constant_24

end SMScattering.Section2
