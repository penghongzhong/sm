import Mathlib.Tactic

/-!
W20 full-master node: v12:cor:relative-cocycle.

The phase identities are proved exactly from the complex exponential law.
Norm preservation after multiplication by a unit phase is standard complex
analysis and is registered separately in the source audit.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open Complex

def phase (x : ℂ) : ℂ := Complex.exp (Complex.I * x)

theorem phase_cocycle (a b c : ℂ) :
    phase (b - a) * phase (c - b) = phase (c - a) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  ring

theorem relative_phase_cocycle
    (qnu qmu pnu pmu : ℂ) :
    phase (qmu - qnu) * phase (pmu - qmu)
      =
    phase (pnu - qnu) * phase (pmu - pnu) := by
  unfold phase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem relative_difference_phase_identity
    (q p Q P : ℂ) :
    Complex.exp (-Complex.I * q) * Q
      - phase (p - q) * (Complex.exp (-Complex.I * p) * P)
      =
    Complex.exp (-Complex.I * q) * (Q - P) := by
  unfold phase
  have hphase :
      Complex.exp (Complex.I * (p - q))
        * Complex.exp (-Complex.I * p)
      =
      Complex.exp (-Complex.I * q) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (-Complex.I * q) * Q
        - Complex.exp (Complex.I * (p - q))
            * (Complex.exp (-Complex.I * p) * P)
      =
      Complex.exp (-Complex.I * q) * Q
        - (Complex.exp (Complex.I * (p - q))
            * Complex.exp (-Complex.I * p)) * P := by ring
    _ =
      Complex.exp (-Complex.I * q) * Q
        - Complex.exp (-Complex.I * q) * P := by rw [hphase]
    _ = Complex.exp (-Complex.I * q) * (Q - P) := by ring

#print axioms phase_cocycle
#print axioms relative_phase_cocycle
#print axioms relative_difference_phase_identity

end SMScattering.W20Full
