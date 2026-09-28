import Mathlib.Tactic

/-!
W20 full-master node: v12:prop:countermodel.

This file checks the finite combinatorial core of the explicit counterexample:
if N pairwise selected cells each carry at least c^2 squared localized norm,
then the l2 cell sum is at least N c^2, hence grows linearly in N at the
squared level (equivalently like sqrt N before squaring).

The construction of smooth translated packets with common compact Fourier
support is a separate standard smooth-translation/Fourier interface recorded
in the v12 source audit.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open scoped BigOperators

theorem v12_countermodel_many_cells_squared
    {N : ℕ}
    (c : ℝ)
    (cellSq : Fin N → ℝ)
    (hlower : ∀ i, c ^ 2 ≤ cellSq i) :
    (N : ℝ) * c ^ 2 ≤ ∑ i, cellSq i := by
  calc
    (N : ℝ) * c ^ 2 = ∑ _i : Fin N, c ^ 2 := by simp
    _ ≤ ∑ i, cellSq i := by
      exact Finset.sum_le_sum (fun i hi => hlower i)

#print axioms v12_countermodel_many_cells_squared

end SMScattering.W20Full
