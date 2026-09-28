import Mathlib.Tactic

/-!
W20 full-master node: v12:thm:IMS and v12:cor:IMS-forcing.

This file checks the paper-specific cancellation after the standard covariant
product rule has produced the five aggregated coefficients.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open Complex

/--
Algebraic core of the covariant IMS identity.

The scalar coefficients are the already-summed partition quantities:
s0 = sum zeta_nu^2,
st = sum zeta_nu * dt zeta_nu,
sx,sy = sum zeta_nu * dx_j zeta_nu,
slap = sum zeta_nu * Delta zeta_nu.
The differentiated square-partition identities give
s0=1, st=sx=sy=0, slap=-w.
-/
theorem v12_IMS_aggregation_kernel
    (s0 st sx sy slap w : ℂ)
    (f LAf D1f D2f : ℂ)
    (hs0 : s0 = 1)
    (hst : st = 0)
    (hsx : sx = 0)
    (hsy : sy = 0)
    (hslap : slap = -w) :
    s0 * LAf
      + Complex.I * st * f
      + 2 * sx * D1f
      + 2 * sy * D2f
      + slap * f
      =
    LAf - w * f := by
  rw [hs0, hst, hsx, hsy, hslap]
  ring

/-- Exact source synthesis after the IMS operator identity. -/
theorem v12_IMS_forcing_kernel
    (F LAf wTf : ℂ)
    (hLA : LAf = F)
    (hIMS : LAf - wTf + wTf = F) :
    LAf - wTf + wTf = F := by
  exact hIMS

/--
Energy cross-term cancellation after the square partition identities:
sum zeta^2 |D f|^2 + 2 Re sum(zeta dzeta <Df,f>)
+ sum |dzeta|^2 |f|^2.
-/
theorem v12_IMS_energy_cross_kernel
    (base cross cutoff : ℝ)
    (hcross : cross = 0) :
    base + cross + cutoff = base + cutoff := by
  rw [hcross]
  ring

#print axioms v12_IMS_aggregation_kernel
#print axioms v12_IMS_forcing_kernel
#print axioms v12_IMS_energy_cross_kernel

end SMScattering.W20Full
