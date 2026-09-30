import lean.v12.V12_SourceProducts

/-!
Precisely registered external theorem, not a new axiom declaration.
Source: Terence Tao, An Epsilon of Room I, Corollary1.11.18, printedp182,
author/AMS-authorized preliminary edition, PDFpageindex190:
https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf
The source permits complex f. Alpha denotes the kernel exponent, NOT the
potential order. This is its dimension2 specialization with Lebesgue measure.
The proposition below has no proof declaration or instance: consumers must
explicitly carry this registered external foundation. Paper-specific kernel,
coefficient and spacetime applications are not part of the interface.
-/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_fractionalPotential (α : ℝ) (f : V12Spatial → ℂ) (x : V12Spatial) : ℂ :=
  ∫ y, f y / ((‖x-y‖ ^ α : ℝ) : ℂ)

/-- Exact external HLS schema, n=2. This definition asserts no axiom. -/
def V12ExternalHLS2D : Prop :=
  ∀ p r α : ℝ, 1 < p → 1 < r → 0 < α → α < 2 →
    1 / p + α / 2 = 1 + 1 / r →
    ∃ C : ℝ, 0 < C ∧ ∀ f : V12Spatial → ℂ,
      MemLp f (ENNReal.ofReal p) (volume : Measure V12Spatial) →
      (∀ᵐ x ∂(volume : Measure V12Spatial),
        Integrable (fun y => f y / ((‖x-y‖ ^ α : ℝ) : ℂ)) (volume : Measure V12Spatial)) ∧
      MemLp (v12_fractionalPotential α f) (ENNReal.ofReal r) (volume : Measure V12Spatial) ∧
      eLpNorm (v12_fractionalPotential α f) (ENNReal.ofReal r) (volume : Measure V12Spatial) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (volume : Measure V12Spatial)

/-- All exponent and dimension conditions for the paper's Hodge application. -/
theorem v12_externalHLS_hodge_exponents (hHLS : V12ExternalHLS2D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : V12Spatial → ℂ,
      MemLp f ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) →
      (∀ᵐ x ∂(volume : Measure V12Spatial),
        Integrable (fun y => f y / ((‖x-y‖ : ℝ) : ℂ)) (volume : Measure V12Spatial)) ∧
      MemLp (v12_fractionalPotential 1 f) 4 (volume : Measure V12Spatial) ∧
      eLpNorm (v12_fractionalPotential 1 f) 4 (volume : Measure V12Spatial) ≤
        ENNReal.ofReal C * eLpNorm f ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) := by
  have h := hHLS ((4 : ℝ) / 3) 4 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hp : ENNReal.ofReal ((4 : ℝ) / 3) = (4 : ℝ≥0∞) / 3 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  simpa only [hp, ENNReal.ofReal_ofNat, Real.rpow_one] using h

#print axioms v12_externalHLS_hodge_exponents
end SMScattering.W20Full
