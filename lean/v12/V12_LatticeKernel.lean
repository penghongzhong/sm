import Mathlib.Tactic

/-!
W20 full-master node: v12:lem:lattice.

The mixed-norm embeddings themselves are standard vector-valued
Minkowski/Cauchy--Schwarz interfaces.  This file checks the exact pointwise
square-partition identity used before those standard norm inequalities.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open scoped BigOperators

theorem v12_lattice_partition_square_kernel
    {ι : Type*} [Fintype ι]
    (zeta : ι → ℝ)
    (F2 : ℝ)
    (hpartition : (∑ i, (zeta i) ^ 2) = 1) :
    (∑ i, (zeta i) ^ 2 * F2) = F2 := by
  rw [← Finset.sum_mul]
  rw [hpartition]
  ring

/--
Abstract synthesis pointwise core after Cauchy--Schwarz:
if the partition square sum is one and Cauchy--Schwarz has produced
|sum zeta_i v_i|^2 <= (sum zeta_i^2) * (sum |v_i|^2),
the coefficient reduces exactly to one.
-/
theorem v12_lattice_synthesis_coefficient_kernel
    (lhs rhs part : ℝ)
    (hpart : part = 1)
    (hcs : lhs ≤ part * rhs) :
    lhs ≤ rhs := by
  simpa [hpart] using hcs

#print axioms v12_lattice_partition_square_kernel
#print axioms v12_lattice_synthesis_coefficient_kernel

end SMScattering.W20Full
