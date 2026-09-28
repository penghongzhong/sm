import Mathlib.Tactic

/-!
W20 full-master node: v12:thm:relative.

Finite algebra behind the relative-gauge identities.  The analytic product
rule supplies the derivative symbols; the paper-specific cancellation is
checked here over C.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open Complex

/--
Pointwise algebra for
  D^{A^Q}_alpha (tau p)
    = tau D^{A^P}_alpha p - i deltaA_alpha tau p.
The hypothesis on dtau is exactly
  partial_alpha tau = i tau (A^Q_alpha-A^P_alpha-deltaA_alpha).
-/
theorem v12_relative_D_kernel
    (tau p dp dtau AQ AP deltaA : ℂ)
    (htau :
      dtau = Complex.I * tau * (AQ - AP - deltaA)) :
    dtau * p + tau * dp - Complex.I * AQ * (tau * p)
      =
    tau * (dp - Complex.I * AP * p)
      - Complex.I * deltaA * tau * p := by
  rw [htau]
  ring

/--
Aggregation kernel for the second-order relative connection formula.
The three Q-side terms are supplied by the ordinary product rule.
-/
theorem v12_relative_L_kernel
    (tau p timeP spaceP1 spaceP2 DP1 DP2 : ℂ)
    (deltaA0 deltaA1 deltaA2 divDeltaA : ℂ)
    (timeQ spaceQ1 spaceQ2 : ℂ)
    (htime :
      timeQ = tau * timeP + deltaA0 * tau * p)
    (hspace1 :
      spaceQ1 =
        tau * spaceP1
        - 2 * Complex.I * deltaA1 * tau * DP1
        - Complex.I * divDeltaA * tau * p
        - deltaA1 ^ 2 * tau * p)
    (hspace2 :
      spaceQ2 =
        tau * spaceP2
        - 2 * Complex.I * deltaA2 * tau * DP2
        - deltaA2 ^ 2 * tau * p) :
    timeQ + spaceQ1 + spaceQ2
      =
    tau * (timeP + spaceP1 + spaceP2)
      - 2 * Complex.I *
          (deltaA1 * tau * DP1 + deltaA2 * tau * DP2)
      + (deltaA0 - Complex.I * divDeltaA
          - (deltaA1 ^ 2 + deltaA2 ^ 2)) * tau * p := by
  rw [htime, hspace1, hspace2]
  ring

#print axioms v12_relative_D_kernel
#print axioms v12_relative_L_kernel

end SMScattering.W20Full
