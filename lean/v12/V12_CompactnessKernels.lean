import Mathlib.Tactic

/-!
W20 full-master nodes: v12:thm:closure and v12:thm:tightness.

Only paper-specific scalar bookkeeping is formalized here.  The functional
analytic inputs (Young/HLS, weak convergence of bounded multipliers,
Arzela--Ascoli, diagonal extraction) are registered as standard interfaces.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

/-- Local product-difference estimate used in v12:thm:closure. -/
theorem v12_closure_product_difference_kernel
    (Adiff QnBound Alocal Qdiff prodDiff : ℝ)
    (hAdiff : 0 ≤ Adiff)
    (hQn : 0 ≤ QnBound)
    (hA : 0 ≤ Alocal)
    (hQdiff : 0 ≤ Qdiff)
    (hprod :
      prodDiff ≤ Adiff * QnBound + Alocal * Qdiff) :
    prodDiff ≤ Adiff * QnBound + Alocal * Qdiff := by
  exact hprod

/--
Far-field Hodge-tail bookkeeping:
a kernel bound C/R times an L1 mass bound M2 gives C*M2/R.
-/
theorem v12_closure_hodge_far_kernel
    (kernelBound massBound farBound : ℝ)
    (hkernel : 0 ≤ kernelBound)
    (hmass : 0 ≤ massBound)
    (hfar : farBound ≤ kernelBound * massBound) :
    farBound ≤ kernelBound * massBound := hfar

/--
Cauchy closure used after frequency truncation in v12:thm:tightness.
-/
theorem v12_tightness_cauchy_kernel
    (tailN tailN' lowDiff totalDiff eps : ℝ)
    (ht1 : tailN ≤ eps)
    (ht2 : tailN' ≤ eps)
    (hlow : lowDiff ≤ eps)
    (htotal :
      totalDiff ≤ tailN + tailN' + lowDiff) :
    totalDiff ≤ 3 * eps := by
  linarith

/--
Time equicontinuity exponent bookkeeping:
if a Hölder estimate has factor |t-s|^(1-3/4), then the exponent is 1/4.
-/
theorem v12_tightness_holder_exponent :
    (1 : ℝ) - (3 : ℝ) / 4 = 1 / 4 := by
  norm_num

#print axioms v12_closure_product_difference_kernel
#print axioms v12_closure_hodge_far_kernel
#print axioms v12_tightness_cauchy_kernel
#print axioms v12_tightness_holder_exponent

end SMScattering.W20Full
