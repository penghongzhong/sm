import Mathlib.Tactic

/-!
W20 full-master node: v12:prop:axial.

The exact gauge identities come from the ordinary FTC/product rule and the
curvature definitions.  This file checks the nontrivial scale bookkeeping in
the square budgets after those standard-analysis steps.

Notation:
  ell      = 2^{-m},
  invEll   = 2^m,
  carrier  = 2^k,
so ell * invEll = 1 and (because m=k-Lambda, Lambda>=4)
1 <= ell * carrier.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

theorem v12_axial_square_budget_kernel
    (ell invEll carrier C Z2 : ℝ)
    (Bnorm dBnorm FrhoNorm FsNorm ArhoNorm dArhoNorm A0Norm : ℝ)
    (hell0 : 0 ≤ ell)
    (hinv0 : 0 ≤ invEll)
    (hcarrier0 : 0 ≤ carrier)
    (hC0 : 0 ≤ C)
    (hZ0 : 0 ≤ Z2)
    (hellinv : ell * invEll = 1)
    (hgap : 1 ≤ ell * carrier)
    (hB : Bnorm ≤ C * Z2)
    (hdB : dBnorm ≤ C * invEll * Z2)
    (hFrho : FrhoNorm ≤ C * carrier * Z2)
    (hFs : FsNorm ≤ C * invEll * Z2)
    (hArho : ArhoNorm ≤ ell * Bnorm)
    (hdArho : dArhoNorm ≤ ell * dBnorm)
    (hA0 : A0Norm ≤ ell * FrhoNorm + ell * FsNorm) :
    ArhoNorm ≤ C * ell * Z2 ∧
    dArhoNorm ≤ C * Z2 ∧
    A0Norm ≤ 2 * C * (ell * carrier) * Z2 := by
  have hArho' : ArhoNorm ≤ C * ell * Z2 := by
    calc
      ArhoNorm ≤ ell * Bnorm := hArho
      _ ≤ ell * (C * Z2) :=
        mul_le_mul_of_nonneg_left hB hell0
      _ = C * ell * Z2 := by ring

  have hdArho' : dArhoNorm ≤ C * Z2 := by
    calc
      dArhoNorm ≤ ell * dBnorm := hdArho
      _ ≤ ell * (C * invEll * Z2) :=
        mul_le_mul_of_nonneg_left hdB hell0
      _ = C * (ell * invEll) * Z2 := by ring
      _ = C * Z2 := by rw [hellinv]; ring

  have hfirst :
      ell * FrhoNorm ≤ C * (ell * carrier) * Z2 := by
    calc
      ell * FrhoNorm ≤ ell * (C * carrier * Z2) :=
        mul_le_mul_of_nonneg_left hFrho hell0
      _ = C * (ell * carrier) * Z2 := by ring

  have hsecond0 : ell * FsNorm ≤ C * Z2 := by
    calc
      ell * FsNorm ≤ ell * (C * invEll * Z2) :=
        mul_le_mul_of_nonneg_left hFs hell0
      _ = C * (ell * invEll) * Z2 := by ring
      _ = C * Z2 := by rw [hellinv]; ring

  have hscale0 : 0 ≤ C * Z2 := mul_nonneg hC0 hZ0
  have hsecond :
      ell * FsNorm ≤ C * (ell * carrier) * Z2 := by
    calc
      ell * FsNorm ≤ C * Z2 := hsecond0
      _ = (C * Z2) * 1 := by ring
      _ ≤ (C * Z2) * (ell * carrier) :=
        mul_le_mul_of_nonneg_left hgap hscale0
      _ = C * (ell * carrier) * Z2 := by ring

  have hA0' : A0Norm ≤ 2 * C * (ell * carrier) * Z2 := by
    calc
      A0Norm ≤ ell * FrhoNorm + ell * FsNorm := hA0
      _ ≤ C * (ell * carrier) * Z2
          + C * (ell * carrier) * Z2 :=
        add_le_add hfirst hsecond
      _ = 2 * C * (ell * carrier) * Z2 := by ring

  exact ⟨hArho', hdArho', hA0'⟩

#print axioms v12_axial_square_budget_kernel

end SMScattering.W20Full
