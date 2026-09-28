import Mathlib.Tactic

/-!
W20 full-master v15 finite algebra:
- cross quadratic expansion in ordered-pair form;
- mixed first-order residual with the cross connection;
- carrier-size transport phase cancellation;
- screened-superposition -> mixed-forcing dependency;
- final frequency-tightness triangle bookkeeping.

The passage from ordered pairs to the paper's a<b notation is ordinary finite
reindexing. Translation/profile orthogonality and the standard L2 profile
decomposition remain explicitly registered external analysis inputs.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open scoped BigOperators

theorem v15_cross_bilinear_ordered
    {ι : Type*} [Fintype ι]
    (uBar v : ι → ℂ) :
    (∑ a, uBar a) * (∑ b, v b) - ∑ a, uBar a * v a
      =
    ∑ a, uBar a * ((∑ b, v b) - v a) := by
  rw [Finset.sum_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

theorem v15_cross_square_ordered
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ) :
    (∑ a, u a) * (∑ b, u b) - ∑ a, u a * u a
      =
    ∑ a, u a * ((∑ b, u b) - u a) := by
  rw [Finset.sum_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

theorem v15_mixed_first_order_with_cross
    {ι : Type*} [Fintype ι]
    (A dU : ι → ℂ) (Across : ℂ) :
    ((∑ a, A a) + Across) * (∑ b, dU b)
        - ∑ a, A a * dU a
      =
    (∑ a, A a * ((∑ b, dU b) - dU a))
        + Across * (∑ b, dU b) := by
  rw [add_mul, Finset.sum_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

theorem v15_screen_carrier_cancel
    (A0 Axi dtChi xiGrad : ℝ)
    (htransport :
      dtChi + 2 * xiGrad = A0 + 2 * Axi) :
    -A0 + dtChi - 2 * Axi + 2 * xiGrad = 0 := by
  linarith

/--
Logical assembly of v15:prop:mix-reduction after the analytic pairwise
orthogonality estimates have been supplied.
-/
theorem v15_mix_forcing_reduction_dependency
    (Realized ScreenSup CrossSmall MixedForc : Prop)
    (hRealized : Realized)
    (hScreen : ScreenSup)
    (hCross : Realized → CrossSmall)
    (hAssemble :
      Realized → ScreenSup → CrossSmall → MixedForc) :
    MixedForc :=
  hAssemble hRealized hScreen (hCross hRealized)

theorem v15_frequency_tightness_triangle
    (tailQ strongDiff tailPhi eps : ℝ)
    (htotal : tailQ ≤ strongDiff + tailPhi)
    (hdiff : strongDiff ≤ eps)
    (hphi : tailPhi ≤ eps) :
    tailQ ≤ 2 * eps := by
  linarith

#print axioms v15_cross_bilinear_ordered
#print axioms v15_cross_square_ordered
#print axioms v15_mixed_first_order_with_cross
#print axioms v15_screen_carrier_cancel
#print axioms v15_mix_forcing_reduction_dependency
#print axioms v15_frequency_tightness_triangle

end SMScattering.W20Full
