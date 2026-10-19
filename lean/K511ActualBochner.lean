import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false

open MeasureTheory
namespace SM.K.Actual511

variable {α : Type*} [MeasurableSpace α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual Bochner integral, not a finite sum or an abstract functional.
No additional axiom is introduced. -/
def integralWeightedKernel (μ : Measure α) (m : α → ℝ) (H : α → E) : E :=
  ∫ y, m y • H y ∂μ

/-- Absolute Bochner integrability and its sharp triangle/norm bound.
The weighted kernel's measurability is derived from the scalar L¹
assumption and the strongly measurable Hessian kernel. -/
theorem integralWeightedKernel_norm_le
    (μ : Measure α) (m : α → ℝ) (H : α → E) (B : ℝ)
    (hm : Integrable m μ)
    (hmnn : ∀ y, 0 ≤ m y)
    (hB : 0 ≤ B)
    (hHmeas : StronglyMeasurable H)
    (hHbound : ∀ y, ‖H y‖ ≤ B) :
    Integrable (fun y => m y • H y) μ ∧
      ‖integralWeightedKernel μ m H‖ ≤ B * (∫ y, m y ∂μ) := by
  have hMeas : AEStronglyMeasurable (fun y => m y • H y) μ :=
    hm.aestronglyMeasurable.smul hHmeas.aestronglyMeasurable
  have hPointwise (y : α) : ‖m y • H y‖ ≤ B * m y := by
    calc
      ‖m y • H y‖ = |m y| * ‖H y‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = m y * ‖H y‖ := by rw [abs_of_nonneg (hmnn y)]
      _ ≤ m y * B := mul_le_mul_of_nonneg_left (hHbound y) (hmnn y)
      _ = B * m y := mul_comm _ _
  have hIntegrable : Integrable (fun y => m y • H y) μ := by
    apply Integrable.mono' (hm.const_mul B) hMeas
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB (hmnn y))] using
      hPointwise y
  refine ⟨hIntegrable, ?_⟩
  calc
    ‖integralWeightedKernel μ m H‖ ≤ ∫ y, ‖m y • H y‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * m y ∂μ :=
      integral_mono hIntegrable.norm (hm.const_mul B) hPointwise
    _ = B * (∫ y, m y ∂μ) := integral_const_mul _ _

/-- The trace-free property of the ACTUAL Lebesgue integral of the
two Hessian components. The sole integrability hypotheses on the two
entries must subsequently be proved using the preceding norm bound. -/
theorem realMatrixIntegral_tracefree
    (μ : Measure α) (m : α → ℝ)
    (H : α → Fin 2 → Fin 2 → ℝ)
    (h00 : Integrable (fun y => m y * H y 0 0) μ)
    (h11 : Integrable (fun y => m y * H y 1 1) μ)
    (hTrace : ∀ y, H y 0 0 + H y 1 1 = 0) :
    (∫ y, m y * H y 0 0 ∂μ) +
        (∫ y, m y * H y 1 1 ∂μ) = 0 := by
  rw [← integral_add h00 h11]
  have hZero : (fun y => m y * H y 0 0 + m y * H y 1 1) =
      (fun _ => (0 : ℝ)) := by
    funext y
    calc
      m y * H y 0 0 + m y * H y 1 1 =
          m y * (H y 0 0 + H y 1 1) := by ring
      _ = 0 := by rw [hTrace y]; ring
  rw [hZero]
  simp

/-- Pointwise symmetry passes to the actual Lebesgue integral without
any extra Bochner/operator exchange hypothesis. -/
theorem realMatrixIntegral_symmetric
    (μ : Measure α) (m : α → ℝ)
    (H : α → Fin 2 → Fin 2 → ℝ)
    (hSym : ∀ y, H y 0 1 = H y 1 0) :
    (∫ y, m y * H y 0 1 ∂μ) =
        (∫ y, m y * H y 1 0 ∂μ) := by
  have hEq : (fun y => m y * H y 0 1) =
      (fun y => m y * H y 1 0) := by
    funext y
    rw [hSym y]
  rw [hEq]

#print axioms SM.K.Actual511.integralWeightedKernel_norm_le
#print axioms SM.K.Actual511.realMatrixIntegral_tracefree
#print axioms SM.K.Actual511.realMatrixIntegral_symmetric

/-- For any genuinely integrable nonnegative density and any entrywise
strongly measurable uniformly bounded tracefree symmetric real Hessian,
the ACTUAL Lebesgue convolution has the exact trace/symmetry identities.
The two entry integrability proofs are obtained from Bochner domination;
they are not listed as assumptions. -/
theorem realMatrixConvolution_tracefree_symmetric
    (μ : Measure α) (m : α → ℝ)
    (H : α → Fin 2 → Fin 2 → ℝ) (B : ℝ)
    (hm : Integrable m μ)
    (hmnn : ∀ y, 0 ≤ m y)
    (hB : 0 ≤ B)
    (hStrong : ∀ i j, StronglyMeasurable (fun y => H y i j))
    (hBound : ∀ y i j, |H y i j| ≤ B)
    (hSym : ∀ y, H y 0 1 = H y 1 0)
    (hTrace : ∀ y, H y 0 0 + H y 1 1 = 0) :
    (∫ y, m y * H y 0 1 ∂μ) = (∫ y, m y * H y 1 0 ∂μ) ∧
      (∫ y, m y * H y 0 0 ∂μ) +
        (∫ y, m y * H y 1 1 ∂μ) = 0 := by
  have hI00 : Integrable (fun y => m y * H y 0 0) μ := by
    have hb : ∀ y, ‖H y 0 0‖ ≤ B := by
      intro y
      simpa only [Real.norm_eq_abs] using hBound y 0 0
    have hh := (integralWeightedKernel_norm_le μ m
      (fun y => H y 0 0) B hm hmnn hB (hStrong 0 0) hb).1
    simpa only [smul_eq_mul] using hh
  have hI11 : Integrable (fun y => m y * H y 1 1) μ := by
    have hb : ∀ y, ‖H y 1 1‖ ≤ B := by
      intro y
      simpa only [Real.norm_eq_abs] using hBound y 1 1
    have hh := (integralWeightedKernel_norm_le μ m
      (fun y => H y 1 1) B hm hmnn hB (hStrong 1 1) hb).1
    simpa only [smul_eq_mul] using hh
  exact ⟨realMatrixIntegral_symmetric μ m H hSym,
    realMatrixIntegral_tracefree μ m H hI00 hI11 hTrace⟩

/-- Use the true L² mass density |q|², not an assumed L¹ surrogate. -/
theorem realMatrixConvolution_from_L2
    (μ : Measure α) (q : α → E)
    (H : α → Fin 2 → Fin 2 → ℝ) (B : ℝ)
    (hq : MemLp q 2 μ)
    (hB : 0 ≤ B)
    (hStrong : ∀ i j, StronglyMeasurable (fun y => H y i j))
    (hBound : ∀ y i j, |H y i j| ≤ B)
    (hSym : ∀ y, H y 0 1 = H y 1 0)
    (hTrace : ∀ y, H y 0 0 + H y 1 1 = 0) :
    (∫ y, ‖q y‖ ^ 2 * H y 0 1 ∂μ) =
        (∫ y, ‖q y‖ ^ 2 * H y 1 0 ∂μ) ∧
      (∫ y, ‖q y‖ ^ 2 * H y 0 0 ∂μ) +
        (∫ y, ‖q y‖ ^ 2 * H y 1 1 ∂μ) = 0 := by
  have hm : Integrable (fun y => ‖q y‖ ^ 2) μ :=
    hq.integrable_norm_pow (by norm_num)
  exact realMatrixConvolution_tracefree_symmetric μ
    (fun y => ‖q y‖ ^ 2) H B hm
    (fun y => sq_nonneg _) hB hStrong hBound hSym hTrace

#print axioms SM.K.Actual511.realMatrixConvolution_tracefree_symmetric
#print axioms SM.K.Actual511.realMatrixConvolution_from_L2


/-- Exact two-dimensional real tracefree matrix norm identity, with
the sharp coefficient one and no dimension-dependent loss. -/
theorem tracefree_real_sqnorm
    (a b v₀ v₁ : ℝ) :
    (a * v₀ + b * v₁) ^ 2 + (b * v₀ - a * v₁) ^ 2 =
      (a ^ 2 + b ^ 2) * (v₀ ^ 2 + v₁ ^ 2) := by
  ring

/-- The sharp Lebesgue/Bochner bound for the two coefficient fields of
a real symmetric tracefree 2x2 Hessian: H = [[a,b],[b,-a]].
It uses the genuine L² mass, with no finite-sum approximation. -/
theorem actual_tracefree_coeff_convolution_bound
    (μ : Measure α) (q : α → E)
    (K : α → EuclideanSpace ℝ (Fin 2)) (B : ℝ)
    (hq : MemLp q 2 μ) (hB : 0 ≤ B)
    (hKStrong : StronglyMeasurable K)
    (hKBound : ∀ y, ‖K y‖ ≤ B) :
    ‖∫ y, (‖q y‖ ^ 2) • K y ∂μ‖ ≤
      B * (∫ y, ‖q y‖ ^ 2 ∂μ) := by
  have hm : Integrable (fun y => ‖q y‖ ^ 2) μ :=
    hq.integrable_norm_pow (by norm_num)
  exact (integralWeightedKernel_norm_le μ (fun y => ‖q y‖ ^ 2)
    K B hm (fun y => sq_nonneg _) hB hKStrong hKBound).2

#print axioms SM.K.Actual511.tracefree_real_sqnorm
#print axioms SM.K.Actual511.actual_tracefree_coeff_convolution_bound


/-- Original 5.11 tensor Z, including the trace subtraction. -/
def originalZ (q d : Fin 2 → ℂ) (j k : Fin 2) : ℝ :=
  2 * ((star (q j)) * d k).im -
    (if j = k then 1 else 0) * (∑ l : Fin 2, ((star (q l)) * d l).im)

/-- The actual matrix-valued convolution, defined entrywise by Lebesgue
integration and NOT by a finite-sum stand-in. -/
def actualTracefreeMatrix (μ : Measure α) (q : α → E)
    (H : α → α → Fin 2 → Fin 2 → ℝ) (x : α) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∫ y, (‖q y‖ ^ 2) * H x y i j ∂μ

/-- A generic two-by-two matrix has the exact contraction cancellation
whenever its trace vanishes. -/
theorem tracefreeZ_contract_exact
    (U : Matrix (Fin 2) (Fin 2) ℝ) (q d : Fin 2 → ℂ)
    (hTrace : U 0 0 + U 1 1 = 0) :
    -2 * (∑ j : Fin 2, ∑ k : Fin 2, U j k * originalZ q d j k) =
      -4 * (∑ j : Fin 2, ∑ k : Fin 2,
        U j k * ((star (q j)) * d k).im) := by
  simp only [originalZ, Fin.sum_univ_two]
  simp only [show (0 : Fin 2) = 0 from rfl,
    show (1 : Fin 2) = 1 from rfl, ↓reduceIte]
  dsimp
  have h11 : U 1 1 = -U 0 0 := by linarith [hTrace]
  rw [h11]
  ring

/-- Original Z contraction in terms of the ACTUAL Lebesgue convolution:
the trace cancellation is not inserted as an assumption, but follows
from the uniform tracefree kernel bound and q in L². -/
theorem actualLebesgue_Z_contract
    (μ : Measure α) (q : α → E)
    (H : α → α → Fin 2 → Fin 2 → ℝ) (B : ℝ)
    (hq : MemLp q 2 μ) (hB : 0 ≤ B)
    (hStrong : ∀ x i j, StronglyMeasurable (fun y => H x y i j))
    (hBound : ∀ x y i j, |H x y i j| ≤ B)
    (hSym : ∀ x y, H x y 0 1 = H x y 1 0)
    (hTrace : ∀ x y, H x y 0 0 + H x y 1 1 = 0)
    (x : α) (v d : Fin 2 → ℂ) :
    -2 * (∑ j : Fin 2, ∑ k : Fin 2,
      actualTracefreeMatrix μ q H x j k * originalZ v d j k) =
      -4 * (∑ j : Fin 2, ∑ k : Fin 2,
      actualTracefreeMatrix μ q H x j k *
        ((star (v j)) * d k).im) := by
  have hInt := realMatrixConvolution_from_L2 μ q (H x) B
    hq hB (hStrong x) (hBound x) (hSym x) (hTrace x)
  exact tracefreeZ_contract_exact (actualTracefreeMatrix μ q H x) v d hInt.2

#print axioms SM.K.Actual511.tracefreeZ_contract_exact
#print axioms SM.K.Actual511.actualLebesgue_Z_contract


/-- Isometry identity for the complex action of a *real* tracefree
symmetric matrix [[a,b],[b,-a]]. This is the sharp 2D step required
to avoid a spurious sqrt(2) loss in the edge estimate. -/
theorem tracefree_complex_sqnorm
    (a b : ℝ) (z w : ℂ) :
    ‖(a : ℂ) * z + (b : ℂ) * w‖ ^ 2 +
      ‖(b : ℂ) * z - (a : ℂ) * w‖ ^ 2 =
      (a ^ 2 + b ^ 2) * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

#print axioms SM.K.Actual511.tracefree_complex_sqnorm


/-- The exact complex-linear action of a real 2x2 symmetric tracefree
matrix on the complex Euclidean plane. -/
abbrev ComplexPlane2 := EuclideanSpace ℂ (Fin 2)
def tracefreeComplexAction (a b : ℝ) (v : ComplexPlane2) : ComplexPlane2 :=
  !₂[(a : ℂ) * v 0 + (b : ℂ) * v 1,
     (b : ℂ) * v 0 - (a : ℂ) * v 1]

private theorem plane2_norm_sq (v : ComplexPlane2) :
    ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]

theorem tracefreeComplexAction_norm_sq (a b : ℝ) (v : ComplexPlane2) :
    ‖tracefreeComplexAction a b v‖ ^ 2 =
      (a ^ 2 + b ^ 2) * ‖v‖ ^ 2 := by
  rw [plane2_norm_sq, plane2_norm_sq v]
  simpa [tracefreeComplexAction] using
    (tracefree_complex_sqnorm a b (v 0) (v 1))

/-- Sharp pointwise operator bound; exactly one coefficient norm,
without a sqrt(2) or a Frobenius norm loss. -/
theorem tracefreeComplexAction_norm_le
    (a b : ℝ) (v : ComplexPlane2) :
    ‖tracefreeComplexAction a b v‖ ≤
      Real.sqrt (a ^ 2 + b ^ 2) * ‖v‖ := by
  have hs := tracefreeComplexAction_norm_sq a b v
  have hp : (Real.sqrt (a ^ 2 + b ^ 2) * ‖v‖) ^ 2 =
      (a ^ 2 + b ^ 2) * ‖v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [norm_nonneg (tracefreeComplexAction a b v),
    Real.sqrt_nonneg (a ^ 2 + b ^ 2), norm_nonneg v]

#print axioms SM.K.Actual511.tracefreeComplexAction_norm_le

end SM.K.Actual511
