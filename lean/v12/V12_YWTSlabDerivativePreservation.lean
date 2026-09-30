import lean.v12.V12_YWSmoothSlabExtension
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Zero extension does not alter any local differential equation in the
open time slab. The first and second derivative statements are proved
from equality on an open neighbourhood, with no derivative assumptions. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory

theorem v12_open_eqOn_fderiv
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set V12Spacetime) (hU : IsOpen U)
    (f g : V12Spacetime → E) (he : Set.EqOn f g U) :
    Set.EqOn (fderiv ℝ f) (fderiv ℝ g) U := by
  intro z hz
  have hn : f =ᶠ[nhds z] g := Filter.Eventually.mono (hU.mem_nhds hz) (fun x hx => he hx)
  exact hn.fderiv_eq

theorem v12_open_eqOn_second_directional_derivative
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set V12Spacetime) (hU : IsOpen U)
    (f g : V12Spacetime → E) (he : Set.EqOn f g U)
    (v w : V12Spacetime) :
    Set.EqOn (fun z => fderiv ℝ (fun x => fderiv ℝ f x v) z w)
      (fun z => fderiv ℝ (fun x => fderiv ℝ g x v) z w) U := by
  have hfirst := v12_open_eqOn_fderiv U hU f g he
  have hd : Set.EqOn (fun x => fderiv ℝ f x v) (fun x => fderiv ℝ g x v) U :=
    fun x hx => congrArg (fun L : V12Spacetime →L[ℝ] E => L v) (hfirst hx)
  intro z hz
  exact congrArg (fun L : V12Spacetime →L[ℝ] E => L w)
    (v12_open_eqOn_fderiv U hU _ _ hd hz)

theorem v12_smoothSlabExtension_eqOn_interior
    (a b : ℝ) (q : V12Spacetime → V12Field) :
    Set.EqOn (v12_smoothSlabExtension a b q) q (Prod.fst ⁻¹' Set.Ioo a b) := by
  intro z hz
  exact v12_smoothSlabExtension_apply a b q z.1 ⟨le_of_lt hz.1, le_of_lt hz.2⟩ z.2

theorem v12_smoothSlabExtension_contDiffOn
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q (Prod.fst ⁻¹' Set.Ioo a b)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (v12_smoothSlabExtension a b q) (Prod.fst ⁻¹' Set.Ioo a b) :=
  hq.congr (v12_smoothSlabExtension_eqOn_interior a b q)

theorem v12_smoothSlabExtension_fderiv
    (a b : ℝ) (q : V12Spacetime → V12Field) :
    Set.EqOn (fderiv ℝ (v12_smoothSlabExtension a b q)) (fderiv ℝ q)
      (Prod.fst ⁻¹' Set.Ioo a b) :=
  v12_open_eqOn_fderiv _
    (isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ)))
    _ _ (v12_smoothSlabExtension_eqOn_interior a b q)

theorem v12_smoothSlabExtension_second_derivative
    (a b : ℝ) (q : V12Spacetime → V12Field) (v w : V12Spacetime) :
    Set.EqOn (fun z => fderiv ℝ (fun x => fderiv ℝ (v12_smoothSlabExtension a b q) x v) z w)
      (fun z => fderiv ℝ (fun x => fderiv ℝ q x v) z w) (Prod.fst ⁻¹' Set.Ioo a b) :=
  v12_open_eqOn_second_directional_derivative _
    (isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ)))
    _ _ (v12_smoothSlabExtension_eqOn_interior a b q) v w

theorem v12_smoothSlabExtension_A_eqOn_interior
    (a b : ℝ) (q : V12Spacetime → V12Field) (j : Fin 2) :
    Set.EqOn (v12_actualCoulombA (v12_smoothSlabExtension a b q) j)
      (v12_actualCoulombA q j) (Prod.fst ⁻¹' Set.Ioo a b) := by
  intro z hz
  exact v12_smoothSlabExtension_A a b q z.1 ⟨le_of_lt hz.1, le_of_lt hz.2⟩ z.2 j

theorem v12_smoothSlabExtension_A_contDiffOn
    (a b : ℝ) (q : V12Spacetime → V12Field) (j : Fin 2)
    (hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (v12_actualCoulombA q j) (Prod.fst ⁻¹' Set.Ioo a b)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (v12_actualCoulombA (v12_smoothSlabExtension a b q) j)
      (Prod.fst ⁻¹' Set.Ioo a b) :=
  hA.congr (v12_smoothSlabExtension_A_eqOn_interior a b q j)

theorem v12_smoothSlabExtension_A_fderiv
    (a b : ℝ) (q : V12Spacetime → V12Field) (j : Fin 2) :
    Set.EqOn (fderiv ℝ (v12_actualCoulombA (v12_smoothSlabExtension a b q) j))
      (fderiv ℝ (v12_actualCoulombA q j)) (Prod.fst ⁻¹' Set.Ioo a b) :=
  v12_open_eqOn_fderiv _
    (isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ)))
    _ _ (v12_smoothSlabExtension_A_eqOn_interior a b q j)

#print axioms v12_open_eqOn_fderiv
#print axioms v12_smoothSlabExtension_second_derivative
#print axioms v12_smoothSlabExtension_A_fderiv
end SMScattering.W20Full
