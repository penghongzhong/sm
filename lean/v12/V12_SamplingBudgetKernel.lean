import Mathlib.Tactic

/-!
W20 full-master node: v12:lem:sampling.

The paper proves the Hilbert-valued sampling estimate by combining:
1. the interval trace/FTC estimate
     ell * sum_c ||f(c ell)||^2
       <= 2 ||f||_2^2 + 2 ell^2 ||f'||_2^2,
2. the band-limited Plancherel derivative estimate
     ell^2 ||f'||_2^2 <= C0^2 ||f||_2^2.

Those two functional-analytic statements are standard-analysis interfaces.
This file checks the paper-specific constant closure exactly.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

theorem v12_sampling_budget_kernel
    (ell C0 sampleSq normSq derivSq : ℝ)
    (htrace :
      ell * sampleSq ≤
        2 * normSq + 2 * (ell ^ 2 * derivSq))
    (hband :
      ell ^ 2 * derivSq ≤ C0 ^ 2 * normSq) :
    ell * sampleSq ≤
      2 * (1 + C0 ^ 2) * normSq := by
  have hband2 :
      2 * (ell ^ 2 * derivSq) ≤
        2 * (C0 ^ 2 * normSq) :=
    mul_le_mul_of_nonneg_left hband (by norm_num)
  calc
    ell * sampleSq
        ≤ 2 * normSq + 2 * (ell ^ 2 * derivSq) := htrace
    _ ≤ 2 * normSq + 2 * (C0 ^ 2 * normSq) :=
      add_le_add_left hband2 (2 * normSq)
    _ = 2 * (1 + C0 ^ 2) * normSq := by ring

#print axioms v12_sampling_budget_kernel

end SMScattering.W20Full
