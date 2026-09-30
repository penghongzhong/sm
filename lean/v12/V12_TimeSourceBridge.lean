import lean.v12.V12_FrequencyTightnessLimit

/-!
W20 Theorem 7.2: exact cutoff source operators and time integration.

The imported core is the byte-identical Run-114 core. The Run-115 additions
are retained below, after their dependencies. Schwartz-to-Lp applications
use explicitly typed Lp elements, not accidental measure arguments.

Certification boundary: the last theorem proves a time Holder estimate from
source-space MemLp and an explicit derivative identity for the actual cutoff
representative. It does NOT prove that identity from the distributional
Coulomb PDE, nor the coefficient source bounds or measurable limit gluing.
-/

set_option autoImplicit false

namespace SMScattering.W20Full

open Filter MeasureTheory FourierTransform LineDeriv Laplacian
open scoped Topology ENNReal

/-- General Schwartz convolution identity, with Lp typing before evaluation. -/
theorem v12_schwartzKernel_rep_eq_schwartzConvolution
    (k : SchwartzMap V12Spatial ℂ)
    (f : SchwartzMap V12Spatial V12Field)
    (x : V12Spatial) :
    v12_L2ConvolutionRep (k.toLp 2) (f.toLp 2) x =
      SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] V12Field →L[ℂ] V12Field) k f x := by
  rw [v12_L2ConvolutionRep_eq_integral,
    SchwartzMap.convolution_apply, MeasureTheory.convolution_eq_swap]
  let k₂ : V12ScalarL2 := k.toLp 2
  have hk0 : (k₂ : V12Spatial → ℂ) =ᵐ[volume] k :=
    k.coeFn_toLp 2 (volume : Measure V12Spatial)
  have hpull :=
    (v12_subLeft_measurePreserving x).quasiMeasurePreserving.ae hk0
  have hk : ∀ᵐ y ∂(volume : Measure V12Spatial),
      k₂ (x - y) = k (x - y) := by
    filter_upwards [hpull] with y hy
    simpa only [v12_subLeftFamily_apply] using hy
  have hf := f.coeFn_toLp 2 (volume : Measure V12Spatial)
  apply integral_congr_ae
  filter_upwards [hk, hf] with y hky hfy
  change k₂ (x - y) • (f.toLp 2 : V12Spatial → V12Field) y = _
  rw [hky, hfy]
  rfl

section DerivativeSemantics

variable (p : V12Spatial → ℝ)
  (hp_cpt : HasCompactSupport p)
  (hp_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
  (N : ℕ)

theorem v12_cutoffKernelLineDeriv_fourier_eq (m : V12Spatial) :
    𝓕 (v12_cutoffKernelLineDerivSchwartz p hp_cpt hp_smooth N m) =
      (2 * Real.pi * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · m)
          (v12_scaledCutoffSchwartz p hp_cpt hp_smooth N) := by
  rw [v12_cutoffKernelLineDerivSchwartz,
    SchwartzMap.fourier_lineDerivOp_eq,
    v12_cutoffKernelSchwartz, fourier_fourierInv_eq]

noncomputable def v12_cutoffLineDerivFourierMultiplier (m : V12Spatial) :
    V12SpatialL2 →L[ℂ] V12SpatialL2 :=
  v12_schwartzKernelFourierMultiplier
    (v12_cutoffKernelLineDerivSchwartz p hp_cpt hp_smooth N m)

theorem v12_cutoffLineDerivFourierMultiplier_on_schwartz_eq_convolution
    (m : V12Spatial) (f : SchwartzMap V12Spatial V12Field) :
    v12_cutoffLineDerivFourierMultiplier p hp_cpt hp_smooth N m (f.toLp 2) =
      (SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] V12Field →L[ℂ] V12Field)
        (v12_cutoffKernelLineDerivSchwartz p hp_cpt hp_smooth N m) f).toLp 2 := by
  simpa [v12_cutoffLineDerivFourierMultiplier] using
    v12_schwartzKernelFourierMultiplier_on_schwartz_eq_convolution
      (v12_cutoffKernelLineDerivSchwartz p hp_cpt hp_smooth N m) f

/-- The source CLM is already defined in the imported core. -/
theorem v12_cutoffLineDerivBCFCLM_on_schwartz_apply
    (m : V12Spatial) (f : SchwartzMap V12Spatial V12Field) (x : V12Spatial) :
    v12_cutoffLineDerivBCFCLM p hp_cpt hp_smooth N m (f.toLp 2) x =
      SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] V12Field →L[ℂ] V12Field)
        (v12_cutoffKernelLineDerivSchwartz p hp_cpt hp_smooth N m) f x := by
  change v12_L2ConvolutionRep
    ((v12_cutoffKernelLineDerivSchwartz p hp_cpt hp_smooth N m).toLp 2)
    (f.toLp 2) x = _
  exact v12_schwartzKernel_rep_eq_schwartzConvolution
    (v12_cutoffKernelLineDerivSchwartz p hp_cpt hp_smooth N m) f x

theorem v12_cutoffLaplacianBCFCLM_on_schwartz_apply
    (f : SchwartzMap V12Spatial V12Field) (x : V12Spatial) :
    v12_cutoffLaplacianBCFCLM p hp_cpt hp_smooth N (f.toLp 2) x =
      SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] V12Field →L[ℂ] V12Field)
        (v12_cutoffKernelLaplacianSchwartz p hp_cpt hp_smooth N) f x := by
  change v12_L2ConvolutionRep
    ((v12_cutoffKernelLaplacianSchwartz p hp_cpt hp_smooth N).toLp 2)
    (f.toLp 2) x = _
  exact v12_schwartzKernel_rep_eq_schwartzConvolution
    (v12_cutoffKernelLaplacianSchwartz p hp_cpt hp_smooth N) f x

end DerivativeSemantics

/-- Actual convolution integral for arbitrary L4/L43 inputs. -/
theorem v12_L4L43ConvolutionRep_eq_integral
    (k : V12ScalarL4) (f : V12SpatialLFourThirds) (x : V12Spatial) :
    v12_L4L43ConvolutionRep k f x =
      ∫ y : V12Spatial, k (x - y) • f y := by
  rw [v12_L4L43ConvolutionRep, v12_L4L43ConvolutionPairing,
    ContinuousLinearMap.lpPairing_eq_integral]
  have hk : (v12_reflectedTranslateL4 k x : V12Spatial → ℂ)
      =ᵐ[volume] fun y => k (x - y) := by
    simpa [v12_reflectedTranslateL4, Function.comp_def] using
      Lp.coeFn_compMeasurePreserving k (v12_subLeft_measurePreserving x)
  apply integral_congr_ae
  filter_upwards [hk] with y hy
  rw [hy]
  rfl

abbrev V12BCF : Type := BoundedContinuousFunction V12Spatial V12Field

/-- Four-term triangle inequality with the exact eLp seminorm. -/
theorem v12_eLpNorm_four_add_le
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (f₀ f₁ f₂ f₃ : Ω → E) :
    eLpNorm (fun t => f₀ t + f₁ t + f₂ t + f₃ t) q μ ≤
      eLpNorm f₀ q μ + eLpNorm f₁ q μ + eLpNorm f₂ q μ + eLpNorm f₃ q μ := by
  calc
    _ ≤ eLpNorm (fun t => f₀ t + f₁ t + f₂ t) q μ + eLpNorm f₃ q μ :=
      eLpNorm_add_le hq
    _ ≤ (eLpNorm (fun t => f₀ t + f₁ t) q μ + eLpNorm f₂ q μ) +
          eLpNorm f₃ q μ := add_le_add_right (eLpNorm_add_le hq) _
    _ ≤ _ := add_le_add_right (add_le_add_right (eLpNorm_add_le hq) _) _

section ActualCutoffSources

variable (p : V12Spatial → ℝ)
  (hp_cpt : HasCompactSupport p)
  (hp_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
  (N : ℕ)

noncomputable def v12_timeLaplacianCLM : V12SpatialL2 →L[ℂ] V12BCF :=
  (Complex.I : ℂ) • v12_cutoffLaplacianBCFCLM p hp_cpt hp_smooth N

noncomputable def v12_timeGradientCLM (j : Fin 2) : V12SpatialL2 →L[ℂ] V12BCF :=
  (2 : ℂ) • v12_cutoffLineDerivBCFCLM p hp_cpt hp_smooth N
    (EuclideanSpace.basisFun (Fin 2) ℝ j)

noncomputable def v12_timeZeroOrderCLM : V12SpatialLFourThirds →L[ℂ] V12BCF :=
  (-Complex.I : ℂ) • v12_cutoffZeroOrderBCFCLM p hp_cpt hp_smooth N

/-- i Delta(K_N)*Q + 2 partial_1(K_N)*F_1 +
2 partial_2(K_N)*F_2 - i K_N*G. Fin 2 indices are 0 and 1. -/
noncomputable def v12_cutoffTimeSource
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds) (t : ℝ) : V12BCF :=
  v12_timeLaplacianCLM p hp_cpt hp_smooth N (Q t) +
    v12_timeGradientCLM p hp_cpt hp_smooth N 0 (F 0 t) +
    v12_timeGradientCLM p hp_cpt hp_smooth N 1 (F 1 t) +
    v12_timeZeroOrderCLM p hp_cpt hp_smooth N (G t)

/-- Explicit finite-measure source budget, before taking toReal. -/
noncomputable def v12_cutoffSourceBudget (μ : Measure ℝ)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds) : ℝ≥0∞ :=
  ENNReal.ofReal ‖v12_timeLaplacianCLM p hp_cpt hp_smooth N‖ *
      (eLpNorm Q ∞ μ * μ Set.univ ^ ((3 : ℝ) / 4)) +
    ENNReal.ofReal ‖v12_timeGradientCLM p hp_cpt hp_smooth N 0‖ *
      (eLpNorm (F 0) 2 μ * μ Set.univ ^ ((1 : ℝ) / 4)) +
    ENNReal.ofReal ‖v12_timeGradientCLM p hp_cpt hp_smooth N 1‖ *
      (eLpNorm (F 1) 2 μ * μ Set.univ ^ ((1 : ℝ) / 4)) +
    ENNReal.ofReal ‖v12_timeZeroOrderCLM p hp_cpt hp_smooth N‖ *
      eLpNorm G ((4 : ℝ≥0∞) / 3) μ

theorem v12_cutoffTimeSource_eLpNorm_le (μ : Measure ℝ)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : AEStronglyMeasurable Q μ)
    (hF : ∀ j, AEStronglyMeasurable (F j) μ)
    (hG : AEStronglyMeasurable G μ) :
    eLpNorm (v12_cutoffTimeSource p hp_cpt hp_smooth N Q F G)
        ((4 : ℝ≥0∞) / 3) μ ≤
      v12_cutoffSourceBudget p hp_cpt hp_smooth N μ Q F G := by
  have hq := v12_eLpNorm_compCLM_fourThirds_of_top μ
    (v12_timeLaplacianCLM p hp_cpt hp_smooth N) Q hQ
  have hf₀ := v12_eLpNorm_compCLM_fourThirds_of_two μ
    (v12_timeGradientCLM p hp_cpt hp_smooth N 0) (F 0) (hF 0)
  have hf₁ := v12_eLpNorm_compCLM_fourThirds_of_two μ
    (v12_timeGradientCLM p hp_cpt hp_smooth N 1) (F 1) (hF 1)
  have hg := v12_eLpNorm_compCLM_le μ
    (v12_timeZeroOrderCLM p hp_cpt hp_smooth N) G
    ((4 : ℝ≥0∞) / 3) hG
  exact (v12_eLpNorm_four_add_le μ ((4 : ℝ≥0∞) / 3)
    v12_one_le_fourThirds_ENNReal
    (fun t => v12_timeLaplacianCLM p hp_cpt hp_smooth N (Q t))
    (fun t => v12_timeGradientCLM p hp_cpt hp_smooth N 0 (F 0 t))
    (fun t => v12_timeGradientCLM p hp_cpt hp_smooth N 1 (F 1 t))
    (fun t => v12_timeZeroOrderCLM p hp_cpt hp_smooth N (G t))).trans
      (add_le_add (add_le_add (add_le_add hq hf₀) hf₁) hg)

theorem v12_cutoffSourceBudget_ne_top (μ : Measure ℝ) [IsFiniteMeasure μ]
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : MemLp Q ∞ μ) (hF : ∀ j, MemLp (F j) 2 μ)
    (hG : MemLp G ((4 : ℝ≥0∞) / 3) μ) :
    v12_cutoffSourceBudget p hp_cpt hp_smooth N μ Q F G ≠ ⊤ := by
  have hq := hQ.eLpNorm_ne_top
  have hf₀ := (hF 0).eLpNorm_ne_top
  have hf₁ := (hF 1).eLpNorm_ne_top
  have hg := hG.eLpNorm_ne_top
  have hm : μ Set.univ ≠ ⊤ := (measure_lt_top μ Set.univ).ne
  unfold v12_cutoffSourceBudget
  finiteness

theorem v12_cutoffTimeSource_memLp (μ : Measure ℝ) [IsFiniteMeasure μ]
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : MemLp Q ∞ μ) (hF : ∀ j, MemLp (F j) 2 μ)
    (hG : MemLp G ((4 : ℝ≥0∞) / 3) μ) :
    MemLp (v12_cutoffTimeSource p hp_cpt hp_smooth N Q F G)
      ((4 : ℝ≥0∞) / 3) μ := by
  exact (v12_cutoffTimeSource_eLpNorm_le p hp_cpt hp_smooth N μ Q F G
    hQ.aestronglyMeasurable (fun j => (hF j).aestronglyMeasurable)
    hG.aestronglyMeasurable).trans_lt
      (lt_top_iff_ne_top.mpr
        (v12_cutoffSourceBudget_ne_top p hp_cpt hp_smooth N μ Q F G hQ hF hG))

/-- Actual low-frequency BCF representative; local L2 identification is in core. -/
noncomputable def v12_cutoffTimeField (Q : ℝ → V12SpatialL2) (t : ℝ) : V12BCF :=
  v12_L2ConvolutionBCFCLM (v12_cutoffKernelL2 p hp_cpt hp_smooth N) (Q t)

end ActualCutoffSources

/-- FTC plus interval Holder. Neither a modulus nor an increment bound is an
input. The actual derivative identity remains an explicit obligation. -/
theorem v12_norm_increment_quarter_of_hasDerivAt_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b : ℝ) (u g : ℝ → E)
    (hg : MemLp g ((4 : ℝ≥0∞) / 3) ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : eLpNorm g ((4 : ℝ≥0∞) / 3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ C)
    (hder : ∀ τ ∈ Set.Icc a b, HasDerivAt u (g τ) τ)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    ‖u t - u s‖ ≤ C.toReal * (t - s) ^ ((1 : ℝ) / 4) := by
  have hsub : ((volume : Measure ℝ).restrict (Set.Ioc s t)) ≤
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
    apply Measure.restrict_mono _ le_rfl
    intro τ hτ
    exact ⟨hs.1.trans hτ.1.le, hτ.2.trans ht.2⟩
  have hlocal : MemLp g ((4 : ℝ≥0∞) / 3)
      ((volume : Measure ℝ).restrict (Set.Ioc s t)) :=
    MemLp.mono_measure hsub hg
  have hint : IntervalIntegrable g volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [Set.uIoc_of_le hst]
    exact memLp_one_iff_integrable.mp
      (hlocal.mono_exponent v12_one_le_fourThirds_ENNReal)
  have hder' : ∀ τ ∈ Set.uIcc s t, HasDerivAt u (g τ) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le hst] at hτ
    exact hder τ ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩
  have hFTC : (∫ τ in s..t, g τ) = u t - u s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder' hint
  have hnorm : ‖∫ τ in s..t, g τ‖ₑ ≤
      C * ENNReal.ofReal (t - s) ^ ((1 : ℝ) / 4) := by
    refine (v12_enorm_intervalIntegral_le_fourThirds_quarter_of_le
      g hst hlocal.aestronglyMeasurable).trans ?_
    exact mul_le_mul_right'
      ((eLpNorm_mono_measure g hsub).trans hbound) _
  have hfinite : C * ENNReal.ofReal (t - s) ^ ((1 : ℝ) / 4) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfinite hnorm
  rw [hFTC] at hreal
  simpa only [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] using hreal

/-- Symmetric endpoint form with one common budget. -/
theorem v12_norm_increment_quarter_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b : ℝ) (u g : ℝ → E)
    (hg : MemLp g ((4 : ℝ≥0∞) / 3) ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : eLpNorm g ((4 : ℝ≥0∞) / 3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ C)
    (hder : ∀ τ ∈ Set.Icc a b, HasDerivAt u (g τ) τ)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    ‖u t - u s‖ ≤ C.toReal * |t - s| ^ ((1 : ℝ) / 4) := by
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
      v12_norm_increment_quarter_of_hasDerivAt_of_le a b u g hg C hC hbound hder hs ht hst
  · have h := v12_norm_increment_quarter_of_hasDerivAt_of_le
      a b u g hg C hC hbound hder ht hs hts
    rw [norm_sub_rev]
    calc
      ‖u s - u t‖ ≤ C.toReal * (s - t) ^ ((1 : ℝ) / 4) := h
      _ = C.toReal * |t - s| ^ ((1 : ℝ) / 4) := by
        rw [abs_sub_comm t s, abs_of_nonneg (sub_nonneg.mpr hts)]

/-- Actual cutoff field/source statement. The original Coulomb PDE must still
supply hder and instantiate the three source MemLp hypotheses from M,Z.
Compiling this theorem does not certify all of W20 Theorem 7.2. -/
theorem v12_cutoff_time_holder_of_source_derivative
    (p : V12Spatial → ℝ) (hp_cpt : HasCompactSupport p)
    (hp_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (N : ℕ) (a b : ℝ)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hF : ∀ j, MemLp (F j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hG : MemLp G ((4 : ℝ≥0∞) / 3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hder : ∀ τ ∈ Set.Icc a b,
      HasDerivAt (v12_cutoffTimeField p hp_cpt hp_smooth N Q)
        (v12_cutoffTimeSource p hp_cpt hp_smooth N Q F G τ) τ)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    ‖v12_cutoffTimeField p hp_cpt hp_smooth N Q t -
        v12_cutoffTimeField p hp_cpt hp_smooth N Q s‖ ≤
      (v12_cutoffSourceBudget p hp_cpt hp_smooth N
        ((volume : Measure ℝ).restrict (Set.Icc a b)) Q F G).toReal *
          |t - s| ^ ((1 : ℝ) / 4) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc a b)
  exact v12_norm_increment_quarter_of_hasDerivAt a b
    (v12_cutoffTimeField p hp_cpt hp_smooth N Q)
    (v12_cutoffTimeSource p hp_cpt hp_smooth N Q F G)
    (v12_cutoffTimeSource_memLp p hp_cpt hp_smooth N μ Q F G hQ hF hG)
    (v12_cutoffSourceBudget p hp_cpt hp_smooth N μ Q F G)
    (v12_cutoffSourceBudget_ne_top p hp_cpt hp_smooth N μ Q F G hQ hF hG)
    (v12_cutoffTimeSource_eLpNorm_le p hp_cpt hp_smooth N μ Q F G
      hQ.aestronglyMeasurable (fun j => (hF j).aestronglyMeasurable)
      hG.aestronglyMeasurable)
    hder hs ht

#print axioms v12_schwartzKernel_rep_eq_schwartzConvolution
#print axioms v12_cutoffKernelLineDeriv_fourier_eq
#print axioms v12_cutoffLineDerivFourierMultiplier_on_schwartz_eq_convolution
#print axioms v12_cutoffLineDerivBCFCLM_on_schwartz_apply
#print axioms v12_cutoffLaplacianBCFCLM_on_schwartz_apply
#print axioms v12_L4L43ConvolutionRep_eq_integral
#print axioms v12_eLpNorm_four_add_le
#print axioms v12_cutoffTimeSource_eLpNorm_le
#print axioms v12_cutoffSourceBudget_ne_top
#print axioms v12_cutoffTimeSource_memLp
#print axioms v12_norm_increment_quarter_of_hasDerivAt_of_le
#print axioms v12_norm_increment_quarter_of_hasDerivAt
#print axioms v12_cutoff_time_holder_of_source_derivative

end SMScattering.W20Full
