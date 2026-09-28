import Mathlib.Tactic

/-!
W20 full-master v18 critical-flow / ESC-RAD support kernels.

The functional-analytic ingredients retained as explicit standard/published
interfaces are:
- the already verified v13 dyadic estimates and sequence Young inequality;
- classical smooth local existence/continuation for smooth Schrodinger maps;
- Banach completeness and diagonal extraction;
- free 2D Strichartz for transfer of an L2 data error to the free L4 norm.

This file checks the paper-specific exponent and bootstrap bookkeeping.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

/-- Exact exponent identity in the weighted high-high-to-low estimate. -/
theorem v18_HHL_weight_exponent
    (s k m : ℤ) :
    s * k + (k - m) =
      s * m + (s + 1) * (k - m) := by
  ring

/-- Scalar absorption used in the weighted small-window persistence estimate. -/
theorem v18_weighted_bootstrap_absorb
    (C alpha theta g : ℝ)
    (hg : 0 ≤ g)
    (htheta : theta ≤ (1 : ℝ) / 2)
    (hboot : g ≤ C * alpha + theta * g) :
    g ≤ 2 * C * alpha := by
  have htg : theta * g ≤ ((1 : ℝ) / 2) * g :=
    mul_le_mul_of_nonneg_right htheta hg
  linarith

/--
The first-exit improvement used for the common local interval:
1/8 + 1/8 = 1/4 < 1/2.
-/
theorem v18_first_exit_improvement
    (eta refNorm diffNorm solNorm : ℝ)
    (heta : 0 < eta)
    (href : refNorm ≤ eta / 8)
    (hdiff : diffNorm ≤ eta / 8)
    (htri : solNorm ≤ refNorm + diffNorm) :
    solNorm < eta / 2 := by
  have hquarter : solNorm ≤ eta / 4 := by
    linarith
  linarith

/-- Cauchy estimate for the rough local-flow completion. -/
theorem v18_rough_local_cauchy
    (C dataDiff flowDiff eps : ℝ)
    (hC : 0 ≤ C)
    (hdata : dataDiff ≤ eps)
    (hflow : flowDiff ≤ C * dataDiff) :
    flowDiff ≤ C * eps := by
  exact le_trans hflow (mul_le_mul_of_nonneg_left hdata hC)

/--
Positive conserved L2 mass obstructs a vanishing total S0 norm whenever
S0 dominates the time-slice L2 norm with a positive constant.
-/
theorem v18_S0_positive_mass_obstruction
    (c mass S : ℝ)
    (hc : 0 < c)
    (hmass : 0 < mass)
    (hdom : c * mass ≤ S) :
    0 < S := by
  exact lt_of_lt_of_le (mul_pos hc hmass) hdom

/-- Exact logical reduction used in ESC-RAD. -/
theorem v18_ESC_reduction_dependency
    (GPEEL TVAN ESCRAD : Prop)
    (hPeel : GPEEL)
    (hVan : TVAN)
    (hReduce : GPEEL → TVAN → ESCRAD) :
    ESCRAD :=
  hReduce hPeel hVan

/-- Exact logical cut-set update after critical-flow deletion and ESC reduction. -/
theorem v18_new_cutset_dependency
    (CritFlow GPEEL TVAN ESC : Prop)
    (hCrit : CritFlow)
    (hPeel : GPEEL)
    (hVan : TVAN)
    (hESC : GPEEL → TVAN → ESC) :
    CritFlow ∧ ESC := by
  exact ⟨hCrit, hESC hPeel hVan⟩

#print axioms v18_HHL_weight_exponent
#print axioms v18_weighted_bootstrap_absorb
#print axioms v18_first_exit_improvement
#print axioms v18_rough_local_cauchy
#print axioms v18_S0_positive_mass_obstruction
#print axioms v18_ESC_reduction_dependency
#print axioms v18_new_cutset_dependency

end SMScattering.W20Full
