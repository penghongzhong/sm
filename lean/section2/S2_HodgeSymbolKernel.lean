import Mathlib.Tactic

/-!
Section 2 Hodge-symbol finite algebra.

At every nonzero real Fourier frequency, div X = 0 and curl X = B form a
2×2 complex linear system. This file solves that system exactly.

No sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

theorem hodge_symbol_unique
    (ξ₁ ξ₂ : ℝ) (X₁ X₂ B : ℂ)
    (hξ : ξ₁^2 + ξ₂^2 ≠ 0)
    (hdiv :
      Complex.I * ((ξ₁ : ℂ) * X₁ + (ξ₂ : ℂ) * X₂) = 0)
    (hcurl :
      Complex.I * ((ξ₁ : ℂ) * X₂ - (ξ₂ : ℂ) * X₁) = B) :
    X₁ =
        (Complex.I * (ξ₂ : ℂ) * B)
          / ((ξ₁ : ℂ)^2 + (ξ₂ : ℂ)^2)
      ∧
    X₂ =
        (-Complex.I * (ξ₁ : ℂ) * B)
          / ((ξ₁ : ℂ)^2 + (ξ₂ : ℂ)^2) := by
  have hI : (Complex.I : ℂ) ≠ 0 := by
    norm_num

  have hdiv' :
      (ξ₁ : ℂ) * X₁ + (ξ₂ : ℂ) * X₂ = 0 := by
    exact (mul_eq_zero.mp hdiv).resolve_left hI

  have hcurl' :
      (ξ₁ : ℂ) * X₂ - (ξ₂ : ℂ) * X₁ = -Complex.I * B := by
    calc
      (ξ₁ : ℂ) * X₂ - (ξ₂ : ℂ) * X₁
          = (-Complex.I) *
              (Complex.I *
                ((ξ₁ : ℂ) * X₂ - (ξ₂ : ℂ) * X₁)) := by
                rw [← mul_assoc]
                norm_num
      _ = -Complex.I * B := by rw [hcurl]

  let d : ℂ := (ξ₁ : ℂ)^2 + (ξ₂ : ℂ)^2

  have hd : d ≠ 0 := by
    intro hd0
    have hd0' :
        (((ξ₁^2 + ξ₂^2 : ℝ) : ℂ)) = 0 := by
      dsimp [d] at hd0
      norm_num at hd0 ⊢
      exact hd0
    have hr : ξ₁^2 + ξ₂^2 = 0 := by
      exact_mod_cast hd0'
    exact hξ hr

  have hx1 :
      d * X₁ = Complex.I * (ξ₂ : ℂ) * B := by
    dsimp [d]
    linear_combination
      (ξ₁ : ℂ) * hdiv' - (ξ₂ : ℂ) * hcurl'

  have hx2 :
      d * X₂ = -Complex.I * (ξ₁ : ℂ) * B := by
    dsimp [d]
    linear_combination
      (ξ₂ : ℂ) * hdiv' + (ξ₁ : ℂ) * hcurl'

  constructor
  · apply (eq_div_iff hd).2
    calc
      X₁ * d = d * X₁ := by ring
      _ = Complex.I * (ξ₂ : ℂ) * B := hx1
  · apply (eq_div_iff hd).2
    calc
      X₂ * d = d * X₂ := by ring
      _ = -Complex.I * (ξ₁ : ℂ) * B := hx2

#print axioms hodge_symbol_unique

end SMScattering.Section2
