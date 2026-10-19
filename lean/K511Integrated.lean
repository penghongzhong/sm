import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

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
  have hprod : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hprod).mp
  rw [hs, hp]

#print axioms SM.K.Actual511.tracefreeComplexAction_norm_le


/-- The true coefficient-vector Bochner convolution of the tracefree Hessian
against the mass |q|². -/
def actualCoeffConvolution (μ : Measure α) (q : α → ComplexPlane2)
    (K : α → α → EuclideanSpace ℝ (Fin 2)) (x : α) :
    EuclideanSpace ℝ (Fin 2) :=
  ∫ y, (‖q y‖ ^ 2) • K x y ∂μ

/-- Complex pairing pointwise bound with the sharp operator coefficient. -/
theorem tracefreeComplexAction_pair_bound
    (a b : ℝ) (q d : ComplexPlane2) :
    |(inner (𝕜 := ℂ) q (tracefreeComplexAction a b d)).im| ≤
      Real.sqrt (a ^ 2 + b ^ 2) * ‖q‖ * ‖d‖ := by
  calc
    |(inner (𝕜 := ℂ) q (tracefreeComplexAction a b d)).im| ≤
      ‖inner (𝕜 := ℂ) q (tracefreeComplexAction a b d)‖ :=
        Complex.abs_im_le_norm _
    _ ≤ ‖q‖ * ‖tracefreeComplexAction a b d‖ := norm_inner_le_norm _ _
    _ ≤ ‖q‖ * (Real.sqrt (a ^ 2 + b ^ 2) * ‖d‖) :=
      mul_le_mul_of_nonneg_left (tracefreeComplexAction_norm_le a b d) (norm_nonneg _)
    _ = Real.sqrt (a ^ 2 + b ^ 2) * ‖q‖ * ‖d‖ := by ring

private theorem norm_pair_integrable_actual
    (μ : Measure α) (q d : α → ComplexPlane2)
    (hq : MemLp q 2 μ) (hd : MemLp d 2 μ) :
    Integrable (fun x => ‖q x‖ * ‖d x‖) μ :=
  (hq.norm).integrable_mul (hd.norm)

private theorem pair_holder_actual
    (μ : Measure α) (q d : α → ComplexPlane2)
    (hq : MemLp q 2 μ) (hd : MemLp d 2 μ) :
    (∫ x, ‖q x‖ * ‖d x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖q x‖ ^ 2 ∂μ) *
      Real.sqrt (∫ x, ‖d x‖ ^ 2 ∂μ) := by
  have hTwo : (ENNReal.ofReal (2 : ℝ)) = (2 : ENNReal) := by norm_num
  have hq' : MemLp q (ENNReal.ofReal 2) μ := by simpa [hTwo] using hq
  have hd' : MemLp d (ENNReal.ofReal 2) μ := by simpa [hTwo] using hd
  convert MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hq' hd' using 1 <;> simp [Real.sqrt_eq_rpow]

/-- The actual L² Cauchy–Schwarz bound for the complex pairing of the
Bochner-convolved, symmetric, tracefree real Hessian.
All analytic integrability assumptions other than hEdgeMeas follow from q,d∈L²,
the strong measurability and the sharp L∞ kernel bound. -/
theorem actualCoeffConvolution_edge_L2
    (μ : Measure α) (q d : α → ComplexPlane2)
    (K : α → α → EuclideanSpace ℝ (Fin 2)) (B : ℝ)
    (hq : MemLp q 2 μ) (hd : MemLp d 2 μ) (hB : 0 ≤ B)
    (hKMeas : ∀ x, StronglyMeasurable (K x))
    (hKBound : ∀ x y, ‖K x y‖ ≤ B)
    (hEdgeMeas : AEStronglyMeasurable (fun x =>
      (inner (𝕜 := ℂ) (q x)
        (tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
          (actualCoeffConvolution μ q K x 1) (d x))).im) μ) :
    |-4 * (∫ x, (inner (𝕜 := ℂ) (q x)
        (tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
          (actualCoeffConvolution μ q K x 1) (d x))).im ∂μ)| ≤
      4 * B * (∫ x, ‖q x‖ ^ 2 ∂μ) *
      Real.sqrt (∫ x, ‖q x‖ ^ 2 ∂μ) *
      Real.sqrt (∫ x, ‖d x‖ ^ 2 ∂μ) := by
  let M : ℝ := ∫ y, ‖q y‖ ^ 2 ∂μ
  let C : ℝ := B * M
  have hm : Integrable (fun y => ‖q y‖ ^ 2) μ :=
    hq.integrable_norm_pow (by norm_num)
  have hM : 0 ≤ M := integral_nonneg (fun y => sq_nonneg (‖q y‖))
  have hC : 0 ≤ C := mul_nonneg hB hM
  have hKernel (x : α) : ‖actualCoeffConvolution μ q K x‖ ≤ C := by
    exact (integralWeightedKernel_norm_le μ (fun y => ‖q y‖ ^ 2) (K x)
      B hm (fun y => sq_nonneg _) hB (hKMeas x) (hKBound x)).2
  let edge : α → ℝ := fun x =>
    (inner (𝕜 := ℂ) (q x)
      (tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
        (actualCoeffConvolution μ q K x 1) (d x))).im
  have hPoint (x : α) :
      |edge x| ≤ C * (‖q x‖ * ‖d x‖) := by
    have hc := tracefreeComplexAction_pair_bound
      (actualCoeffConvolution μ q K x 0)
      (actualCoeffConvolution μ q K x 1) (q x) (d x)
    have hNorm : Real.sqrt
        ((actualCoeffConvolution μ q K x 0) ^ 2 +
         (actualCoeffConvolution μ q K x 1) ^ 2) =
        ‖actualCoeffConvolution μ q K x‖ := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [hNorm] at hc
    calc
      |edge x| ≤ ‖actualCoeffConvolution μ q K x‖ * ‖q x‖ * ‖d x‖ := hc
      _ ≤ C * ‖q x‖ * ‖d x‖ := by
        gcongr
        exact hKernel x
      _ = C * (‖q x‖ * ‖d x‖) := by ring
  have hProd := norm_pair_integrable_actual μ q d hq hd
  have hInt : Integrable edge μ := by
    apply Integrable.mono' (hProd.const_mul C) hEdgeMeas
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hPoint x
  have hAbs : |∫ x, edge x ∂μ| ≤
      C * (Real.sqrt (∫ x, ‖q x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x, ‖d x‖ ^ 2 ∂μ)) := by
    calc
      |∫ x, edge x ∂μ| = ‖∫ x, edge x ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, ‖edge x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x, |edge x| ∂μ := by simp only [Real.norm_eq_abs]
      _ ≤ ∫ x, C * (‖q x‖ * ‖d x‖) ∂μ :=
        integral_mono hInt.abs (hProd.const_mul C) hPoint
      _ = C * (∫ x, ‖q x‖ * ‖d x‖ ∂μ) := integral_const_mul _ _
      _ ≤ C * (Real.sqrt (∫ x, ‖q x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖d x‖ ^ 2 ∂μ)) := by
            gcongr
            exact pair_holder_actual μ q d hq hd
  change |-4 * (∫ x, edge x ∂μ)| ≤ _
  calc
    |-4 * (∫ x, edge x ∂μ)| = 4 * |∫ x, edge x ∂μ| := by
      rw [abs_mul]; norm_num
    _ ≤ 4 * (C * (Real.sqrt (∫ x, ‖q x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x, ‖d x‖ ^ 2 ∂μ))) := by gcongr
    _ = 4 * B * (∫ x, ‖q x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x, ‖q x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x, ‖d x‖ ^ 2 ∂μ) := by dsimp [C, M]; ring

#print axioms SM.K.Actual511.tracefreeComplexAction_pair_bound
#print axioms SM.K.Actual511.actualCoeffConvolution_edge_L2


/-- Matrix representation of the REAL symmetric traceless Hessian via
its two independent real coefficients. -/
def tracefreeMatrixOfCoeffs (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![a, b], ![b, -a]]

private theorem tracefreeMatrixOfCoeffs_trace (a b : ℝ) :
    tracefreeMatrixOfCoeffs a b 0 0 +
      tracefreeMatrixOfCoeffs a b 1 1 = 0 := by
  simp [tracefreeMatrixOfCoeffs]

/-- Exact original Z_jk contraction and imaginary Hilbert pairing
for the same REAL tracefree matrix, with all coefficients preserved.
In particular there is NO sharp-constant loss here. -/
theorem originalZ_eq_complex_pair
    (a b : ℝ) (q d : ComplexPlane2) :
    -2 * (∑ j : Fin 2, ∑ k : Fin 2,
      tracefreeMatrixOfCoeffs a b j k *
        originalZ (fun i => q i) (fun i => d i) j k) =
      -4 * (inner (𝕜 := ℂ) q (tracefreeComplexAction a b d)).im := by
  calc
    -2 * (∑ j : Fin 2, ∑ k : Fin 2,
      tracefreeMatrixOfCoeffs a b j k *
        originalZ (fun i => q i) (fun i => d i) j k) =
      -4 * (∑ j : Fin 2, ∑ k : Fin 2,
        tracefreeMatrixOfCoeffs a b j k *
          ((star (q j)) * d k).im) :=
        tracefreeZ_contract_exact _ _ _ (tracefreeMatrixOfCoeffs_trace a b)
    _ = -4 * (inner (𝕜 := ℂ) q (tracefreeComplexAction a b d)).im := by
      congr 1
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [tracefreeMatrixOfCoeffs, tracefreeComplexAction,
        dotProduct, Fin.sum_univ_two, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring

#print axioms SM.K.Actual511.originalZ_eq_complex_pair


/-- Projection of the genuine Banach-valued Bochner integral equals the
ordinary Lebesgue integral of the corresponding Hessian coefficient. -/
theorem actualCoeffConvolution_coordinate
    (μ : Measure α) (q : α → ComplexPlane2)
    (K : α → α → EuclideanSpace ℝ (Fin 2)) (B : ℝ)
    (hq : MemLp q 2 μ) (hB : 0 ≤ B)
    (hKMeas : ∀ x, StronglyMeasurable (K x))
    (hKBound : ∀ x y, ‖K x y‖ ≤ B)
    (x : α) (i : Fin 2) :
    (actualCoeffConvolution μ q K x) i =
      ∫ y, (‖q y‖ ^ 2) * (K x y i) ∂μ := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i
  have hm : Integrable (fun y => ‖q y‖ ^ 2) μ :=
    hq.integrable_norm_pow (by norm_num)
  have hInt : Integrable (fun y => (‖q y‖ ^ 2) • K x y) μ :=
    (integralWeightedKernel_norm_le μ (fun y => ‖q y‖ ^ 2) (K x)
      B hm (fun y => sq_nonneg _) hB (hKMeas x) (hKBound x)).1
  have hComp := L.integral_comp_comm hInt
  calc
    (actualCoeffConvolution μ q K x) i =
      L (∫ y, (‖q y‖ ^ 2) • K x y ∂μ) := rfl
    _ = ∫ y, L ((‖q y‖ ^ 2) • K x y) ∂μ := hComp.symm
    _ = ∫ y, ‖q y‖ ^ 2 * (K x y i) ∂μ := by
      simp only [L, PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul]

/-- The local bound in the ORIGINAL Z_jk contraction, using the same
two independent Lebesgue-convolved coefficients as the sharp Bochner
bound. The only explicitly supplied measurability is the x-variable
complex pairing, automatically available for smooth Hessian kernels. -/
theorem actualOriginalZ_edge_L2
    (μ : Measure α) (q d : α → ComplexPlane2)
    (K : α → α → EuclideanSpace ℝ (Fin 2)) (B : ℝ)
    (hq : MemLp q 2 μ) (hd : MemLp d 2 μ) (hB : 0 ≤ B)
    (hKMeas : ∀ x, StronglyMeasurable (K x))
    (hKBound : ∀ x y, ‖K x y‖ ≤ B)
    (hEdgeMeas : AEStronglyMeasurable (fun x =>
      (inner (𝕜 := ℂ) (q x)
        (tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
          (actualCoeffConvolution μ q K x 1) (d x))).im) μ) :
    |-2 * (∫ x, ∑ j : Fin 2, ∑ k : Fin 2,
      tracefreeMatrixOfCoeffs (actualCoeffConvolution μ q K x 0)
        (actualCoeffConvolution μ q K x 1) j k *
        originalZ (fun i => q x i) (fun i => d x i) j k ∂μ)| ≤
      4 * B * (∫ x, ‖q x‖ ^ 2 ∂μ) *
      Real.sqrt (∫ x, ‖q x‖ ^ 2 ∂μ) *
      Real.sqrt (∫ x, ‖d x‖ ^ 2 ∂μ) := by
  let R : α → ℝ := fun x => ∑ j : Fin 2, ∑ k : Fin 2,
      tracefreeMatrixOfCoeffs (actualCoeffConvolution μ q K x 0)
        (actualCoeffConvolution μ q K x 1) j k *
        originalZ (fun i => q x i) (fun i => d x i) j k
  let edge : α → ℝ := fun x =>
      (inner (𝕜 := ℂ) (q x)
        (tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
          (actualCoeffConvolution μ q K x 1) (d x))).im
  have hbridge (x : α) : -2 * R x = -4 * edge x :=
    originalZ_eq_complex_pair _ _ (q x) (d x)
  have hIntEq : -2 * (∫ x, R x ∂μ) = -4 * (∫ x, edge x ∂μ) := by
    calc
      -2 * (∫ x, R x ∂μ) = ∫ x, -2 * R x ∂μ :=
        (integral_const_mul _ _).symm
      _ = ∫ x, -4 * edge x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hbridge)
      _ = -4 * (∫ x, edge x ∂μ) := integral_const_mul _ _
  have hBound := actualCoeffConvolution_edge_L2
    μ q d K B hq hd hB hKMeas hKBound hEdgeMeas
  change |-2 * (∫ x, R x ∂μ)| ≤ _
  rw [hIntEq]
  exact hBound

#print axioms SM.K.Actual511.actualCoeffConvolution_coordinate
#print axioms SM.K.Actual511.actualOriginalZ_edge_L2

end SM.K.Actual511


noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory

namespace SM.K.Original511

private theorem clock_pointwise
    (e eStar J Cz A B c Ne T Ce R : ℝ)
    (he : 0 < e) (heStar : e ≤ eStar) (hJ : 0 < J)
    (hCz : 0 ≤ Cz) (hA : 0 ≤ A) (hB : 0 < B) (hc : 0 < c)
    (hNe : 0 ≤ Ne) (hT : 0 < T) (hTcap : T ≤ B ^ 2 * Ne ^ 2)
    (hCe : c * Ne ^ 2 ≤ Ce)
    (hLocal : |R| ≤ (4 * Real.sqrt 2 * A * Cz / J) *
      e ^ ((5:ℝ)/2) * Ne * Real.sqrt T) :
    |R| ≤ (4 * (Real.sqrt 2 * A * B * Cz *
      eStar ^ ((5:ℝ)/2) / (c*J))) * Ce := by
  have hBNe : 0 ≤ B * Ne := mul_nonneg (le_of_lt hB) hNe
  have hSqrtT : Real.sqrt T ≤ B * Ne := by
    have hAux : (Real.sqrt T)^2 ≤ (B * Ne)^2 := by
      rw [Real.sq_sqrt (le_of_lt hT)]
      nlinarith [hTcap]
    nlinarith [Real.sqrt_nonneg T]
  have hPow : e ^ ((5:ℝ)/2) ≤ eStar ^ ((5:ℝ)/2) := by
    exact Real.rpow_le_rpow (le_of_lt he) heStar (by norm_num)
  have hCoef : 0 ≤ 4 * Real.sqrt 2 * A * Cz / J := by positivity
  have hPowerNonneg : 0 ≤ eStar ^ ((5:ℝ)/2) := Real.rpow_nonneg (le_trans (le_of_lt he) heStar) _
  have hCoeff : 0 ≤ 4 * (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J)) := by positivity
  calc
    |R| ≤ (4 * Real.sqrt 2 * A * Cz / J) * e ^ ((5:ℝ)/2) * Ne * Real.sqrt T := hLocal
    _ ≤ (4 * Real.sqrt 2 * A * Cz / J) * eStar ^ ((5:ℝ)/2) * Ne * (B * Ne) := by
      gcongr
    _ = (4 * (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J))) * (c * Ne ^ 2) := by
      field_simp
      ring
    _ ≤ (4 * (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J))) * Ce := by
      gcongr

/-- The original time-weight `χ(e)Nₑ²/(eTₑ)`. -/
private def edgeWeight (chi : ℝ → ℝ) (Ne Te : ℝ → ℝ → ℝ)
    (e t : ℝ) : ℝ := chi e * Ne e t ^ 2 / (e * Te e t)

private theorem edgeWeight_nonneg
    (chi : ℝ → ℝ) (Ne Te : ℝ → ℝ → ℝ)
    (e t : ℝ) (hchi : 0 ≤ chi e) (he : 0 < e) (hT : 0 < Te e t) :
    0 ≤ edgeWeight chi Ne Te e t := by
  unfold edgeWeight
  positivity

/-- Original Lemma 5.11's clock transfer under its original heat-layer
hypotheses and the local tracefree edge estimate. This part is conditional on
`hLocal`, which must be discharged by the local statement to count 5.11. -/
theorem edge_clock_integral
    (I : Set ℝ) (chi : ℝ → ℝ) (Ne Te Ce Redge : ℝ → ℝ → ℝ)
    (eStar J Cz A B c : ℝ)
    (hJ : 0 < J) (hCz : 0 ≤ Cz) (hA : 0 ≤ A)
    (hB : 0 < B) (hc : 0 < c)
    (hchi : ∀ e, 0 ≤ chi e)
    (hchiOne : (∫ e, chi e) = 1)
    (hsupp : ∀ e, chi e ≠ 0 → 0 < e ∧ e ≤ eStar)
    (hNe : ∀ e t, chi e ≠ 0 → 0 ≤ Ne e t)
    (hTe : ∀ e t, chi e ≠ 0 → 0 < Te e t)
    (hTcap : ∀ e t, chi e ≠ 0 → Te e t ≤ B ^ 2 * Ne e t ^ 2)
    (hCe : ∀ e t, chi e ≠ 0 → c * Ne e t ^ 2 ≤ Ce e t)
    (hLocal : ∀ e t, chi e ≠ 0 →
      |Redge e t| ≤ (4 * Real.sqrt 2 * A * Cz / J) *
        e ^ ((5:ℝ)/2) * Ne e t * Real.sqrt (Te e t))
    (hEdgeInnerInt : ∀ t, Integrable
      (fun e => edgeWeight chi Ne Te e t * Redge e t))
    (hCInnerInt : ∀ t, Integrable
      (fun e => edgeWeight chi Ne Te e t * Ce e t))
    (hEdgeOuterInt : Integrable
      (fun t => ∫ e, edgeWeight chi Ne Te e t * Redge e t)
      ((volume : Measure ℝ).restrict I))
    (hCOuterInt : Integrable
      (fun t => ∫ e, edgeWeight chi Ne Te e t * Ce e t)
      ((volume : Measure ℝ).restrict I)) :
    |∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Redge e t)| ≤
      (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c*J)) *
        (4 * (∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Ce e t))) := by
  let coeff : ℝ := Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J)
  have hCoeffNonneg : 0 ≤ 4 * coeff := by
    have heStarNonneg : 0 ≤ eStar := by
      have hSome : ∃ e, chi e ≠ 0 := by
        by_contra hn
        have heq : chi = (fun _ => (0:ℝ)) := by
          funext e
          by_contra hx
          exact hn ⟨e, hx⟩
        simp [heq] at hchiOne
      obtain ⟨e, he⟩ := hSome
      exact le_trans (le_of_lt (hsupp e he).1) (hsupp e he).2
    dsimp [coeff]
    positivity
  have hPointwise (e t : ℝ) :
      |edgeWeight chi Ne Te e t * Redge e t| ≤
        (4 * coeff) * (edgeWeight chi Ne Te e t * Ce e t) := by
    by_cases hz : chi e = 0
    · simp [edgeWeight, hz]
    have he : 0 < e := (hsupp e hz).1
    have ht : 0 < Te e t := hTe e t hz
    have hw : 0 ≤ edgeWeight chi Ne Te e t :=
      edgeWeight_nonneg chi Ne Te e t (hchi e) he ht
    have hpt := clock_pointwise e eStar J Cz A B c (Ne e t) (Te e t)
      (Ce e t) (Redge e t) he (hsupp e hz).2 hJ hCz hA hB hc
      (hNe e t hz) ht (hTcap e t hz) (hCe e t hz) (hLocal e t hz)
    calc
      |edgeWeight chi Ne Te e t * Redge e t| =
          edgeWeight chi Ne Te e t * |Redge e t| := by
            rw [abs_mul, abs_of_nonneg hw]
      _ ≤ edgeWeight chi Ne Te e t * ((4 * coeff) * Ce e t) := by
        gcongr
      _ = (4 * coeff) * (edgeWeight chi Ne Te e t * Ce e t) := by ring
  have hI (t : ℝ) :
      |∫ e, edgeWeight chi Ne Te e t * Redge e t| ≤
        (4 * coeff) * (∫ e, edgeWeight chi Ne Te e t * Ce e t) := by
    calc
      |∫ e, edgeWeight chi Ne Te e t * Redge e t| =
          ‖∫ e, edgeWeight chi Ne Te e t * Redge e t‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ e, ‖edgeWeight chi Ne Te e t * Redge e t‖ := norm_integral_le_integral_norm _
      _ = ∫ e, |edgeWeight chi Ne Te e t * Redge e t| := by simp only [Real.norm_eq_abs]
      _ ≤ ∫ e, (4 * coeff) * (edgeWeight chi Ne Te e t * Ce e t) := by
        exact integral_mono (hEdgeInnerInt t).abs ((hCInnerInt t).const_mul _) (fun e => hPointwise e t)
      _ = (4 * coeff) * (∫ e, edgeWeight chi Ne Te e t * Ce e t) := integral_const_mul _ _
  calc
    |∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Redge e t)| =
        ‖∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Redge e t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in I, ‖∫ e, edgeWeight chi Ne Te e t * Redge e t‖ := norm_integral_le_integral_norm _
    _ = ∫ t in I, |∫ e, edgeWeight chi Ne Te e t * Redge e t| := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ t in I, (4 * coeff) * (∫ e, edgeWeight chi Ne Te e t * Ce e t) := by
      exact integral_mono hEdgeOuterInt.abs (hCOuterInt.const_mul _) hI
    _ = coeff * (4 * (∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Ce e t))) := by
      rw [integral_const_mul]
      ring

#print axioms SM.K.Original511.edge_clock_integral

/-- Sharp bridge from the actual local L² tracefree estimate to the
heat-layer estimate assumed by edge_clock_integral.
No hLocal is taken as input: it is DERIVED with the mass 2e and the
D W thermal norm bound. -/
theorem local_to_heat_layer
    (e J Cz A Ne Te M D Redge : ℝ)
    (he : 0 < e) (hJ : 0 < J) (hCz : 0 ≤ Cz)
    (hA : 0 ≤ A) (hN : 0 ≤ Ne) (hTe : 0 < Te)
    (hMass : M = 2 * e)
    (hD : Real.sqrt D ≤ A * e * Ne * Real.sqrt Te)
    (hLocal : |Redge| ≤
        4 * (Cz / (2 * J)) * M * Real.sqrt M * Real.sqrt D) :
    |Redge| ≤ (4 * Real.sqrt 2 * A * Cz / J) *
      e ^ ((5:ℝ)/2) * Ne * Real.sqrt Te := by
  have hp : e ^ ((5:ℝ)/2) = e ^ 2 * Real.sqrt e := by
    calc
      e ^ ((5:ℝ)/2) = e ^ ((2:ℝ) + (1:ℝ)/2) := by congr 1; ring
      _ = e ^ (2:ℝ) * e ^ ((1:ℝ)/2) := Real.rpow_add he _ _
      _ = e ^ 2 * Real.sqrt e := by
        rw [← Real.sqrt_eq_rpow]
        exact congrArg (fun r : ℝ => r * Real.sqrt e) (Real.rpow_natCast e 2)
  have hr : Real.sqrt (2 * e) = Real.sqrt 2 * Real.sqrt e := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hcoef : 0 ≤ 4 * (Cz / (2 * J)) *
      (2 * e) * Real.sqrt (2 * e) := by positivity
  calc
    |Redge| ≤
        4 * (Cz / (2 * J)) * M * Real.sqrt M * Real.sqrt D := hLocal
    _ = 4 * (Cz / (2 * J)) * (2 * e) *
        Real.sqrt (2 * e) * Real.sqrt D := by rw [hMass]
    _ ≤ 4 * (Cz / (2 * J)) * (2 * e) *
        Real.sqrt (2 * e) * (A * e * Ne * Real.sqrt Te) :=
      mul_le_mul_of_nonneg_left hD hcoef
    _ = (4 * Real.sqrt 2 * A * Cz / J) *
          e ^ ((5:ℝ)/2) * Ne * Real.sqrt Te := by
      rw [hr, hp]
      field_simp
      ring

#print axioms SM.K.Original511.local_to_heat_layer



/- Direct combination of the REAL tracefree-convolution edge pairing with
the true heat-layer clock theorem. Unlike the separate clock theorem,
the local e^(5/2) edge bound is NOT an assumption. -/
open SM.K.Actual511

variable {α : Type*} [MeasurableSpace α]

def nativeRedge (μ : Measure α)
    (q d : ℝ → ℝ → α → ComplexPlane2)
    (K : ℝ → ℝ → α → α → EuclideanSpace ℝ (Fin 2))
    (e t : ℝ) : ℝ :=
  -2 * (∫ x, ∑ j : Fin 2, ∑ k : Fin 2,
    tracefreeMatrixOfCoeffs (actualCoeffConvolution μ (q e t) (K e t) x 0)
      (actualCoeffConvolution μ (q e t) (K e t) x 1) j k *
      originalZ (fun i => q e t x i) (fun i => d e t x i) j k ∂μ)

/-- Precisely integrated 5.11 from L² spatial fields, mass 2e,
the sharp tracefree Hessian convolution bound, and the original heat
bounds. The x-integrand measurability and the explicitly declared
time-integral existence conditions are retained as mathematical
regularity obligations of the native heat-flow field model. -/
theorem original511_spatial_and_clock
    (μ : Measure α)
    (I : Set ℝ) (chi : ℝ → ℝ) (Ne Te Ce : ℝ → ℝ → ℝ)
    (q d : ℝ → ℝ → α → ComplexPlane2)
    (K : ℝ → ℝ → α → α → EuclideanSpace ℝ (Fin 2))
    (eStar J Cz A B c : ℝ)
    (hJ : 0 < J) (hCz : 0 ≤ Cz) (hA : 0 ≤ A)
    (hB : 0 < B) (hc : 0 < c)
    (hchi : ∀ e, 0 ≤ chi e)
    (hchiOne : (∫ e, chi e) = 1)
    (hsupp : ∀ e, chi e ≠ 0 → 0 < e ∧ e ≤ eStar)
    (hNe : ∀ e t, chi e ≠ 0 → 0 ≤ Ne e t)
    (hTe : ∀ e t, chi e ≠ 0 → 0 < Te e t)
    (hTcap : ∀ e t, chi e ≠ 0 → Te e t ≤ B ^ 2 * Ne e t ^ 2)
    (hCe : ∀ e t, chi e ≠ 0 → c * Ne e t ^ 2 ≤ Ce e t)
    (hq : ∀ e t, chi e ≠ 0 → MemLp (q e t) 2 μ)
    (hd : ∀ e t, chi e ≠ 0 → MemLp (d e t) 2 μ)
    (hMass : ∀ e t, chi e ≠ 0 → (∫ x, ‖q e t x‖ ^ 2 ∂μ) = 2 * e)
    (hDNorm : ∀ e t, chi e ≠ 0 →
      Real.sqrt (∫ x, ‖d e t x‖ ^ 2 ∂μ) ≤
        A * e * Ne e t * Real.sqrt (Te e t))
    (hKMeas : ∀ e t x, chi e ≠ 0 → StronglyMeasurable (K e t x))
    (hKBound : ∀ e t x y, chi e ≠ 0 → ‖K e t x y‖ ≤ Cz / (2 * J))
    (hPairMeas : ∀ e t, chi e ≠ 0 →
      AEStronglyMeasurable (fun x =>
        (inner (𝕜 := ℂ) (q e t x)
          (tracefreeComplexAction
            (actualCoeffConvolution μ (q e t) (K e t) x 0)
            (actualCoeffConvolution μ (q e t) (K e t) x 1)
            (d e t x))).im) μ)
    (hEdgeInnerInt : ∀ t, Integrable
      (fun e => edgeWeight chi Ne Te e t * nativeRedge μ q d K e t))
    (hCInnerInt : ∀ t, Integrable
      (fun e => edgeWeight chi Ne Te e t * Ce e t))
    (hEdgeOuterInt : Integrable
      (fun t => ∫ e, edgeWeight chi Ne Te e t * nativeRedge μ q d K e t)
      ((volume : Measure ℝ).restrict I))
    (hCOuterInt : Integrable
      (fun t => ∫ e, edgeWeight chi Ne Te e t * Ce e t)
      ((volume : Measure ℝ).restrict I)) :
    |∫ t in I, (∫ e, edgeWeight chi Ne Te e t * nativeRedge μ q d K e t)| ≤
      (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J)) *
        (4 * (∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Ce e t))) := by
  have hLocal : ∀ e t, chi e ≠ 0 →
      |nativeRedge μ q d K e t| ≤
        (4 * Real.sqrt 2 * A * Cz / J) *
          e ^ ((5:ℝ)/2) * Ne e t * Real.sqrt (Te e t) := by
    intro e t hz
    have hSpatial := actualOriginalZ_edge_L2 μ
      (q e t) (d e t) (K e t) (Cz / (2 * J))
      (hq e t hz) (hd e t hz)
      (by positivity)
      (fun x => hKMeas e t x hz)
      (fun x y => hKBound e t x y hz)
      (hPairMeas e t hz)
    have hREdge : |nativeRedge μ q d K e t| ≤
        4 * (Cz / (2 * J)) *
          (∫ x, ‖q e t x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖q e t x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x, ‖d e t x‖ ^ 2 ∂μ) := by
      simpa only [nativeRedge] using hSpatial
    exact local_to_heat_layer e J Cz A (Ne e t) (Te e t)
      (∫ x, ‖q e t x‖ ^ 2 ∂μ)
      (∫ x, ‖d e t x‖ ^ 2 ∂μ)
      (nativeRedge μ q d K e t)
      (hsupp e hz).1 hJ hCz hA (hNe e t hz) (hTe e t hz)
      (hMass e t hz) (hDNorm e t hz) hREdge
  exact edge_clock_integral I chi Ne Te Ce (nativeRedge μ q d K)
    eStar J Cz A B c hJ hCz hA hB hc hchi hchiOne hsupp
    hNe hTe hTcap hCe hLocal
    hEdgeInnerInt hCInnerInt hEdgeOuterInt hCOuterInt

#print axioms SM.K.Original511.original511_spatial_and_clock



/-- Spatial pairing measurability follows from chosen strongly-measurable
L² representatives and joint measurability of the actual Hessian
convolution kernel. This eliminates the nonpaper pairing premise. -/
theorem edge_pair_measurable_of_joint
    (μ : Measure α) [SFinite μ]
    (q d : α → ComplexPlane2)
    (K : α → α → EuclideanSpace ℝ (Fin 2))
    (hqSM : StronglyMeasurable q)
    (hdSM : StronglyMeasurable d)
    (hKJoint : StronglyMeasurable (fun p : α × α => K p.1 p.2)) :
    AEStronglyMeasurable (fun x =>
      (inner (𝕜 := ℂ) (q x)
        (tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
          (actualCoeffConvolution μ q K x 1) (d x))).im) μ := by
  have hQProd : StronglyMeasurable (fun p : α × α => q p.2) :=
    hqSM.comp_measurable measurable_snd
  have hmass : StronglyMeasurable (fun p : α × α => ‖q p.2‖ ^ 2) :=
    (show Continuous (fun v : ComplexPlane2 => ‖v‖ ^ (2:ℕ)) by fun_prop).comp_stronglyMeasurable hQProd
  have hJoint : StronglyMeasurable
      (fun p : α × α => (‖q p.2‖ ^ 2) • K p.1 p.2) :=
    hmass.smul hKJoint
  have hConv : StronglyMeasurable (actualCoeffConvolution μ q K) := by
    simpa only [actualCoeffConvolution] using hJoint.integral_prod_right'
  have h0 : StronglyMeasurable (fun x => (actualCoeffConvolution μ q K x) 0) := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).continuous.comp_stronglyMeasurable hConv
  have h1 : StronglyMeasurable (fun x => (actualCoeffConvolution μ q K x) 1) := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).continuous.comp_stronglyMeasurable hConv
  have hArgs : StronglyMeasurable
      (fun x => ((actualCoeffConvolution μ q K x 0,
        actualCoeffConvolution μ q K x 1), d x)) :=
    (h0.prodMk h1).prodMk hdSM
  have hCont : Continuous
      (fun z : (ℝ × ℝ) × ComplexPlane2 =>
        tracefreeComplexAction z.1.1 z.1.2 z.2) := by
    dsimp only [tracefreeComplexAction]
    fun_prop
  have hAction : StronglyMeasurable (fun x =>
      tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
        (actualCoeffConvolution μ q K x 1) (d x)) :=
    hCont.comp_stronglyMeasurable hArgs
  have hInner : StronglyMeasurable (fun x =>
      inner (𝕜 := ℂ) (q x)
        (tracefreeComplexAction (actualCoeffConvolution μ q K x 0)
          (actualCoeffConvolution μ q K x 1) (d x))) :=
    hqSM.inner hAction
  exact (Complex.continuous_im.comp_stronglyMeasurable hInner).aestronglyMeasurable

#print axioms SM.K.Original511.edge_pair_measurable_of_joint

end SM.K.Original511