import Mathlib.Tactic

/-!
Section 2 finite-algebra kernel for paper Lemma `v12:lem:electric`.

This file verifies only the exact substitution
  F = -4 (e₁ + e₂),
  eℓ = ∂ℓ S_{jℓ} - (1/2) ∂j |Qℓ|²
⇒ F = -4 Σℓ ∂ℓ S_{jℓ} + 2 ∂j m.

The differential product rule and covariant compatibility are not hidden here:
they remain separate analytic/formalization obligations.
No sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

theorem electric_divergence_algebra
    (F e₁ e₂ dS₁ dS₂ dm₁ dm₂ : ℝ)
    (hF : F = -4 * (e₁ + e₂))
    (h₁ : e₁ = dS₁ - ((1 : ℝ) / 2) * dm₁)
    (h₂ : e₂ = dS₂ - ((1 : ℝ) / 2) * dm₂) :
    F = -4 * (dS₁ + dS₂) + 2 * (dm₁ + dm₂) := by
  rw [hF, h₁, h₂]
  ring

#print axioms electric_divergence_algebra

end SMScattering.Section2
