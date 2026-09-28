import Mathlib.Tactic

/-!
W20 full-master v17 support kernels:
- Cauchy completion from full-N stability;
- short collision-layer residual length;
- diagonal two-error closure;
- strict profile-energy inequality.

These kernels do not replace the paper's carrier/Wilson analytic estimates;
they isolate the finite bookkeeping around those estimates.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

theorem v17_rough_flow_cauchy_assembly
    (C dataDiff flowDiff eps : ℝ)
    (hC : 0 ≤ C)
    (hdata : dataDiff ≤ eps)
    (hstab : flowDiff ≤ C * dataDiff) :
    flowDiff ≤ C * eps := by
  exact le_trans hstab (mul_le_mul_of_nonneg_left hdata hC)

theorem v17_collision_layer_length_kernel
    (C tau residual : ℝ)
    (hC : 0 ≤ C)
    (htau : 0 ≤ tau)
    (hres : residual ≤ C * tau) :
    residual ≤ C * tau := hres

theorem v17_diagonal_two_error_kernel
    (screenErr approxErr totalErr eps : ℝ)
    (hscreen : screenErr ≤ eps)
    (happrox : approxErr ≤ eps)
    (htotal : totalErr ≤ screenErr + approxErr) :
    totalErr ≤ 2 * eps := by
  linarith

theorem v17_profile_energy_strict_kernel
    (Ej Eother Ec : ℝ)
    (hOther : 0 < Eother)
    (hLedger : Ej + Eother ≤ Ec) :
    Ej < Ec := by
  linarith

#print axioms v17_rough_flow_cauchy_assembly
#print axioms v17_collision_layer_length_kernel
#print axioms v17_diagonal_two_error_kernel
#print axioms v17_profile_energy_strict_kernel

end SMScattering.W20Full
