import Mathlib.Tactic

/-!
W20 full-master W3 support kernels.

The section is deliberately guardrail-heavy: it corrects invalid localization
and square-sum shortcuts, proves exact coherent/operator algebra, and isolates
the diagonal-transfer estimate as an explicit hypothesis of the first-exit
theorem.

The generic analytic interfaces (free Strichartz, LP square function,
Minkowski/Hölder, bounded real-potential self-adjointness) are registered in
the companion source audit.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open scoped BigOperators

/-- Product-rule aggregation in the cutoff equation. -/
theorem w3_cutoff_source_kernel
    (chi F Rb Cchi lhs : ℂ)
    (hlhs : lhs = chi * (F + Rb) + Cchi) :
    lhs = chi * F + chi * Rb + Cchi := by
  rw [hlhs]
  ring

/-- Near-frequency fourth-power inequality used in the recombination sum. -/
theorem w3_near_pair_kernel (a b : ℝ) :
    a ^ 2 * b ^ 2 ≤ ((a ^ 4 + b ^ 4) / 2) := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

/-- The mixed lateral Hölder reciprocal exponent identity. -/
theorem w3_lateral_holder_exponents :
    (1 : ℝ) / 3 + 1 / 6 = 1 / 2
      ∧
    (1 : ℝ) / 6 + 1 / 3 = 1 / 2 := by
  norm_num

/-- Pointwise finite coherent partition isometry at the squared-norm level. -/
theorem w3_coherent_partition_kernel
    {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (fSq : ℝ)
    (hpart : ∑ i, weight i = 1) :
    ∑ i, weight i * fSq = fSq := by
  rw [← Finset.sum_mul, hpart]
  ring

/--
Compression retains the common connection:
sum w_nu (A-dchi_nu) = A-gamma if sum w_nu=1 and
gamma=sum w_nu dchi_nu.
-/
theorem w3_Berry_connection_retained
    {ι : Type*} [Fintype ι]
    (weight dchi : ι → ℝ) (A gamma : ℝ)
    (hpart : ∑ i, weight i = 1)
    (hgamma : gamma = ∑ i, weight i * dchi i) :
    ∑ i, weight i * (A - dchi i) = A - gamma := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_mul, hpart, one_mul]
  rw [hgamma]

/-- Algebraic stationary identity in the explicit scalar potential model. -/
theorem w3_potential_stationary_kernel
    (s : ℝ) (hs : 1 + s ≠ 0) :
    4 * (s - 1) / (1 + s) ^ 3
      =
    (4 * (s - 1) / (1 + s) ^ 2) * (1 / (1 + s)) := by
  field_simp [hs]

/-- Exact low/high connection split in the true magnetic residual. -/
theorem w3_actual_residual_split_kernel
    (Alow Ahigh b dQ F0 : ℂ) :
    (Alow + Ahigh - b) * dQ + F0
      =
    (Alow - b) * dQ + Ahigh * dQ + F0 := by
  ring

/-- Constant spatial drift conjugacy: both extra coefficients vanish. -/
theorem w3_constant_drift_coefficients
    (Xp b betaP c0 b2 : ℝ)
    (hX : Xp = 2 * b)
    (hbeta : betaP = c0 - b2) :
    Xp - 2 * b = 0
      ∧
    -betaP - b2 + c0 = 0 := by
  constructor <;> linarith

/-- Cubic zero-order forcing scale bookkeeping. -/
theorem w3_zero_order_cubic_kernel
    (C M Z coeffNorm forcingNorm : ℝ)
    (hZ : 0 ≤ Z)
    (hcoeff :
      coeffNorm ≤ C * (1 + M ^ 2) * Z ^ 2)
    (hforcing : forcingNorm ≤ coeffNorm * Z)
    (hC : 0 ≤ C)
    (hM2 : 0 ≤ 1 + M ^ 2) :
    forcingNorm ≤ C * (1 + M ^ 2) * Z ^ 3 := by
  have hmul :
      coeffNorm * Z
        ≤ (C * (1 + M ^ 2) * Z ^ 2) * Z :=
    mul_le_mul_of_nonneg_right hcoeff hZ
  calc
    forcingNorm ≤ coeffNorm * Z := hforcing
    _ ≤ (C * (1 + M ^ 2) * Z ^ 2) * Z := hmul
    _ = C * (1 + M ^ 2) * Z ^ 3 := by ring

/--
The first-exit contradiction core.  Once the diagonal-transfer input and
near/far recombination yield r^4 <= r^4/4 at a positive barrier r, contradiction
is automatic.
-/
theorem w3_first_exit_contradiction_kernel
    (r : ℝ)
    (hr : 0 < r)
    (hbad : r ^ 4 ≤ (1 : ℝ) / 4 * r ^ 4) :
    False := by
  have hr4 : 0 < r ^ 4 := pow_pos hr 4
  nlinarith

/--
The two local norm inequalities in the coherent square-function discussion are
logically independent of the false ell2(L4) reverse estimate.
-/
theorem w3_norm_order_dependency
    (DleX XleY FalseReverse : Prop)
    (hDX : DleX)
    (hXY : XleY) :
    DleX ∧ XleY :=
  ⟨hDX, hXY⟩

/-- Exact statement boundary for the conditional first-exit theorem. -/
theorem w3_first_exit_dependency
    (LocalTheory DiagonalTransfer Recombine NonlinearVanishing : Prop)
    (hLocal : LocalTheory)
    (hDiagonal : DiagonalTransfer)
    (hRecombine :
      LocalTheory → DiagonalTransfer → Recombine)
    (hExit :
      LocalTheory → DiagonalTransfer → Recombine → NonlinearVanishing) :
    NonlinearVanishing :=
  hExit hLocal hDiagonal (hRecombine hLocal hDiagonal)

#print axioms w3_cutoff_source_kernel
#print axioms w3_near_pair_kernel
#print axioms w3_lateral_holder_exponents
#print axioms w3_coherent_partition_kernel
#print axioms w3_Berry_connection_retained
#print axioms w3_potential_stationary_kernel
#print axioms w3_actual_residual_split_kernel
#print axioms w3_constant_drift_coefficients
#print axioms w3_zero_order_cubic_kernel
#print axioms w3_first_exit_contradiction_kernel
#print axioms w3_norm_order_dependency
#print axioms w3_first_exit_dependency

end SMScattering.W20Full
