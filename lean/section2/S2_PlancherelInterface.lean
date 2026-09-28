import Mathlib.Analysis.Fourier.LpSpace

/-!
Section 2 registered standard-analysis interface: Plancherel on L².

This is not a custom axiom.  It is a direct corollary of Mathlib's
`MeasureTheory.Lp.norm_fourier_eq` in the pinned Mathlib revision.
-/

noncomputable section

open FourierTransform MeasureTheory

namespace SMScattering.Section2

variable {E F : Type*}
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem plancherel_L2_registered
    (f : Lp (α := E) F 2) :
    ‖𝓕 f‖ = ‖f‖ := by
  simpa using (MeasureTheory.Lp.norm_fourier_eq f)

#print axioms plancherel_L2_registered

end SMScattering.Section2
