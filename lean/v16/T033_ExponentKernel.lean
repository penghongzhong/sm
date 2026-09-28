import Mathlib.Tactic

/-!
T033 exponent kernel for the weak-profile realization.

For 4/3 < p < 2, the conjugate exponent p' = p/(p-1) lies strictly
below the planar Sobolev exponent p* = 2p/(2-p).  This is exactly the
exponent inequality used to obtain strong local L^{p'} convergence of
the frame from W^{1,p} compactness.

No sorry/admit/custom axiom.
-/

namespace SMScattering.V16

theorem p_conj_lt_sobolev
    (p : ℝ)
    (hp_lo : (4 : ℝ) / 3 < p)
    (hp_hi : p < 2) :
    p / (p - 1) < (2 * p) / (2 - p) := by
  have hp0 : 0 < p := by
    linarith
  have hp1 : 0 < p - 1 := by
    linarith
  have h2p : 0 < 2 - p := by
    linarith
  apply (div_lt_div_iff₀ hp1 h2p).2
  nlinarith

#print axioms p_conj_lt_sobolev

end SMScattering.V16
