import Mathlib.Tactic

/-!
W20 full-master v16 screen continuity kernels.

The analytic inputs in the paper are Fubini, Cauchy--Schwarz and the elementary
unit-phase Lipschitz inequality |exp(i a)-exp(i b)| <= |a-b|.  This file
checks the paper-specific constants and the final norm chaining.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

theorem v16_screen_curvature_pointwise_constant
    (a b : ℝ) :
    4 * a * b ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

theorem v16_screen_phase_bound_assembly
    (thetaNorm bNorm qNorm : ℝ)
    (hTheta : thetaNorm ≤ bNorm)
    (hB : bNorm ≤ 2 * qNorm ^ 2) :
    thetaNorm ≤ 2 * qNorm ^ 2 :=
  le_trans hTheta hB

theorem v16_screen_multiplier_lipschitz_assembly
    (qNorm pNorm diffNorm thetaDiff bDiff fNorm multDiff : ℝ)
    (hf : 0 ≤ fNorm)
    (hTheta : thetaDiff ≤ bDiff)
    (hB : bDiff ≤ 4 * (qNorm + pNorm) * diffNorm)
    (hMult : multDiff ≤ thetaDiff * fNorm) :
    multDiff ≤
      4 * (qNorm + pNorm) * diffNorm * fNorm := by
  have htheta :
      thetaDiff ≤ 4 * (qNorm + pNorm) * diffNorm :=
    le_trans hTheta hB
  calc
    multDiff ≤ thetaDiff * fNorm := hMult
    _ ≤ (4 * (qNorm + pNorm) * diffNorm) * fNorm :=
      mul_le_mul_of_nonneg_right htheta hf
    _ = 4 * (qNorm + pNorm) * diffNorm * fNorm := by ring

theorem v16_bounded_profile_dependency
    (StrongParameterLimit WeakRealization ExactEnergy : Prop)
    (hParam : StrongParameterLimit)
    (hRealize : StrongParameterLimit → WeakRealization)
    (hEnergy : WeakRealization → ExactEnergy) :
    WeakRealization ∧ ExactEnergy := by
  have hR := hRealize hParam
  exact ⟨hR, hEnergy hR⟩

#print axioms v16_screen_curvature_pointwise_constant
#print axioms v16_screen_phase_bound_assembly
#print axioms v16_screen_multiplier_lipschitz_assembly
#print axioms v16_bounded_profile_dependency

end SMScattering.W20Full
