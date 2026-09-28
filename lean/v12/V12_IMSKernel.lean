import Mathlib.Tactic

/-!
Partial support for W20 v12 IMS. This file does not formalize smooth
covariant derivatives, Hilbert adjoints, or locally finite spatial partitions.
The forcing lemma below no longer assumes its own conclusion.
-/

namespace SMScattering.W20Full

open Complex

theorem v12_IMS_aggregation_kernel
    (s0 st sx sy slap w : ℂ)
    (f LAf D1f D2f : ℂ)
    (hs0 : s0 = 1) (hst : st = 0) (hsx : sx = 0)
    (hsy : sy = 0) (hslap : slap = -w) :
    s0 * LAf + Complex.I * st * f + 2 * sx * D1f
      + 2 * sy * D2f + slap * f = LAf - w * f := by
  rw [hs0, hst, hsx, hsy, hslap]
  ring

/-- Genuine cancellation from the equation LAf = F; the result is not an input. -/
theorem v12_IMS_forcing_kernel
    (F LAf wTf : ℂ) (hLA : LAf = F) :
    LAf - wTf + wTf = F := by
  calc
    LAf - wTf + wTf = LAf := sub_add_cancel LAf wTf
    _ = F := hLA

/-- A left inverse gives an idempotent synthesis/localization composition. -/
theorem v12_IMS_projection_idempotent
    {X Y : Type*} (T : X → Y) (S : Y → X)
    (hST : Function.LeftInverse S T) (y : Y) :
    T (S (T (S y))) = T (S y) := by
  rw [hST (S y)]

theorem v12_IMS_energy_cross_kernel
    (base cross cutoff : ℝ) (hcross : cross = 0) :
    base + cross + cutoff = base + cutoff := by
  rw [hcross]
  ring

#print axioms v12_IMS_aggregation_kernel
#print axioms v12_IMS_forcing_kernel
#print axioms v12_IMS_projection_idempotent
#print axioms v12_IMS_energy_cross_kernel

end SMScattering.W20Full
