import Mathlib.Tactic

/-!
W20 full-master v20 support kernels.

The non-algebraic inputs are the already certified v13 forcing estimates,
standard finite partitioning of an L4 function, completeness of the N0 forcing
space, and the free Smith/Strichartz Duhamel estimate.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

theorem v20_finite_forcing_sum_kernel
    {ι : Type*} [Fintype ι]
    (piece : ι → ℝ) (total : ℝ)
    (hTotal : total ≤ ∑ i, piece i) :
    total ≤ ∑ i, piece i :=
  hTotal

theorem v20_Duhamel_tail_kernel
    (C tail increment eps : ℝ)
    (hC : 0 ≤ C)
    (hTail : tail ≤ eps)
    (hDuhamel : increment ≤ C * tail) :
    increment ≤ C * eps := by
  exact le_trans hDuhamel (mul_le_mul_of_nonneg_left hTail hC)

theorem v20_tail_linearization_kernel
    (C tail difference eps : ℝ)
    (hC : 0 ≤ C)
    (hTail : tail ≤ eps)
    (hDifference : difference ≤ C * tail) :
    difference ≤ C * eps := by
  exact le_trans hDifference (mul_le_mul_of_nonneg_left hTail hC)

theorem v20_scattering_state_unique_kernel
    (stateDistance limsupDistance : ℝ)
    (hUnitary : stateDistance = limsupDistance)
    (hLimit : limsupDistance = 0) :
    stateDistance = 0 := by
  rw [hUnitary, hLimit]

theorem v20_subcritical_scattering_dependency
    (GlobalFiniteS FiniteSImpliesScatter Scatter : Prop)
    (hGlobal : GlobalFiniteS)
    (hFinite : GlobalFiniteS → FiniteSImpliesScatter)
    (hScatter : FiniteSImpliesScatter → Scatter) :
    Scatter :=
  hScatter (hFinite hGlobal)

#print axioms v20_finite_forcing_sum_kernel
#print axioms v20_Duhamel_tail_kernel
#print axioms v20_tail_linearization_kernel
#print axioms v20_scattering_state_unique_kernel
#print axioms v20_subcritical_scattering_dependency

end SMScattering.W20Full
