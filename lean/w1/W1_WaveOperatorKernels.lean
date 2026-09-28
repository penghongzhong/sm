import Mathlib.Tactic

/-!
W20 full-master W1 support kernels.

The W1 section uses the already audited internal inputs (A0)--(A4), standard
free dispersive/Fourier estimates, and finite/compactness arguments. This file
checks the scalar first-exit and scale bookkeeping that is specific to W1.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

/-- Relative-error absorption after the nonlinear term has been bounded by z/4. -/
theorem w1_relative_absorb_kernel
    (z C delta nonlinear : ℝ)
    (hineq : z ≤ C * delta + z / 4 + nonlinear)
    (hnonlinear : nonlinear ≤ z / 4) :
    z ≤ 2 * C * delta := by
  linarith

/-- Shadow bootstrap arithmetic: eta/8 reference + eta/8 difference = eta/4. -/
theorem w1_shadow_first_exit_kernel
    (eta refNorm diffNorm qNorm : ℝ)
    (href : refNorm ≤ eta / 8)
    (hdiff : diffNorm ≤ eta / 8)
    (htri : qNorm ≤ refNorm + diffNorm) :
    qNorm ≤ eta / 4 := by
  linarith

/-- Common-tail arithmetic used in the rough wave-operator construction. -/
theorem w1_common_tail_kernel
    (eta refTail perturbTail totalTail : ℝ)
    (href : refTail ≤ eta / 16)
    (hpert : perturbTail ≤ eta / 32)
    (htotal : totalTail ≤ refTail + perturbTail) :
    totalTail ≤ 3 * eta / 32 := by
  linarith

/-- Exact exponent in the fixed-frequency curl estimate. -/
theorem w1_curl_exponent_kernel (k : ℝ) :
    -k + 2 * k * ((3 : ℝ) / 4 - (1 : ℝ) / 2)
      = -k / 2 := by
  ring

/-- Finite-net tail estimate. -/
theorem w1_compact_net_kernel
    (centerTail lipError total eps : ℝ)
    (hcenter : centerTail ≤ eps / 2)
    (hlip : lipError ≤ eps / 2)
    (htotal : total ≤ centerTail + lipError) :
    total ≤ eps := by
  linarith

/-- Escape block error bookkeeping. -/
theorem w1_escape_match_kernel
    (C dataErr compactTail matchErr : ℝ)
    (hC : 0 ≤ C)
    (hmatch : matchErr ≤ C * (dataErr + compactTail)) :
    matchErr ≤ C * (dataErr + compactTail) :=
  hmatch

/-- Dependency assembly for the rough one-sided wave operator. -/
theorem w1_rough_wave_dependency
    (Seed Density FinalStability RoughWave : Prop)
    (hSeed : Seed)
    (hDensity : Density)
    (hFinal : FinalStability)
    (hAssemble : Seed → Density → FinalStability → RoughWave) :
    RoughWave :=
  hAssemble hSeed hDensity hFinal

#print axioms w1_relative_absorb_kernel
#print axioms w1_shadow_first_exit_kernel
#print axioms w1_common_tail_kernel
#print axioms w1_curl_exponent_kernel
#print axioms w1_compact_net_kernel
#print axioms w1_escape_match_kernel
#print axioms w1_rough_wave_dependency

end SMScattering.W20Full
