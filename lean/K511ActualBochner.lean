import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Basic

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

end SM.K.Actual511
