import lean.v12.V12_YNonlinearLocalProducts

/-!
Actual quadratic coefficient classes on a measure space: conjugate(Q_k) Q_j,
its real and imaginary parts, and the mass density. Local strong L2
convergence gives strong L1 convergence by the continuous Holder product.
No coefficient convergence is assumed. Hodge potential convergence is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_curvatureDensity (Q : V12Field) : ℝ :=
  4 * (star (Q 0) * Q 1).im

theorem v12_curvatureDensity_bound (Q : V12Field) :
    ‖v12_curvatureDensity Q‖ ≤ 2 * ‖Q‖ ^ 2 := by
  have hsum : ‖Q‖ ^ 2 = ‖Q 0‖ ^ 2 + ‖Q 1‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  have hi : |(star (Q 0) * Q 1).im| ≤ ‖Q 0‖ * ‖Q 1‖ := by
    simpa only [norm_mul, norm_star] using Complex.abs_im_le_norm (star (Q 0) * Q 1)
  calc
    ‖v12_curvatureDensity Q‖ = 4 * |(star (Q 0) * Q 1).im| := by
      simp [v12_curvatureDensity, Real.norm_eq_abs, abs_mul]
    _ ≤ 4 * (‖Q 0‖ * ‖Q 1‖) := by linarith
    _ ≤ 2 * ‖Q‖ ^ 2 := by nlinarith [sq_nonneg (‖Q 0‖ - ‖Q 1‖)]

#print axioms v12_curvatureDensity_bound

noncomputable def v12_componentL2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j : Fin 2) :
    Lp V12Field 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (EuclideanSpace.proj (𝕜 := ℂ) j).compLpL 2 μ

noncomputable def v12_tensorL1Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (Q : Lp V12Field 2 μ) : Lp ℂ 1 μ :=
  (ContinuousLinearMap.mul ℝ ℂ).holder 1
    (Complex.conjCLE.toContinuousLinearMap.compLp (v12_componentL2 μ k Q))
    (v12_componentL2 μ j Q)

theorem v12_tensorL1Class_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (Q : Lp V12Field 2 μ) :
    (v12_tensorL1Class μ j k Q : Ω → ℂ) =ᵐ[μ]
      fun z => star ((Q z) k) * (Q z) j := by
  have hj := (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL Q
  have hk := (EuclideanSpace.proj (𝕜 := ℂ) k).coeFn_compLpL Q
  have hc := Complex.conjCLE.toContinuousLinearMap.coeFn_compLp (v12_componentL2 μ k Q)
  have hp := (ContinuousLinearMap.mul ℝ ℂ).coeFn_holder (r := 1)
    (Complex.conjCLE.toContinuousLinearMap.compLp (v12_componentL2 μ k Q))
    (v12_componentL2 μ j Q)
  filter_upwards [hj, hk, hc, hp] with z hzj hzk hzc hzp
  change v12_tensorL1Class μ j k Q z = star ((Q z) k) * (Q z) j
  change v12_componentL2 μ j Q z = (Q z) j at hzj
  change v12_componentL2 μ k Q z = (Q z) k at hzk
  change (Complex.conjCLE.toContinuousLinearMap.compLp (v12_componentL2 μ k Q)) z =
    star (v12_componentL2 μ k Q z) at hzc
  change v12_tensorL1Class μ j k Q z =
    (Complex.conjCLE.toContinuousLinearMap.compLp (v12_componentL2 μ k Q)) z *
      v12_componentL2 μ j Q z at hzp
  rw [hzp, hzc, hzj, hzk]

theorem v12_tensorL1Class_continuous
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2) :
    Continuous (v12_tensorL1Class μ j k) := by
  have hl := (Complex.conjCLE.toContinuousLinearMap.compLpL 2 μ).continuous.comp
    (v12_componentL2 μ k).continuous
  have hr := (v12_componentL2 μ j).continuous
  have h := ((ContinuousLinearMap.mul ℝ ℂ).holderL μ 2 2 1).continuous₂.comp (hl.prodMk hr)
  simpa only [Function.comp_def, Function.uncurry, ContinuousLinearMap.holderL_apply_apply,
    v12_tensorL1Class] using h

noncomputable def v12_B_L1Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : Lp V12Field 2 μ) : Lp ℝ 1 μ :=
  (4 : ℝ) • Complex.imCLM.compLp (v12_tensorL1Class μ 1 0 Q)

noncomputable def v12_S_L1Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (Q : Lp V12Field 2 μ) : Lp ℝ 1 μ :=
  Complex.reCLM.compLp (v12_tensorL1Class μ j k Q)

noncomputable def v12_massL1Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : Lp V12Field 2 μ) : Lp ℝ 1 μ :=
  v12_S_L1Class μ 0 0 Q + v12_S_L1Class μ 1 1 Q

theorem v12_quadratic_coefficients_strong_L1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Qn : ℕ → Lp V12Field 2 μ) (Q : Lp V12Field 2 μ)
    (hQ : Tendsto Qn atTop (𝓝 Q)) :
    Tendsto (fun n => v12_B_L1Class μ (Qn n)) atTop (𝓝 (v12_B_L1Class μ Q)) ∧
    (∀ j k, Tendsto (fun n => v12_S_L1Class μ j k (Qn n)) atTop
      (𝓝 (v12_S_L1Class μ j k Q))) ∧
    Tendsto (fun n => v12_massL1Class μ (Qn n)) atTop (𝓝 (v12_massL1Class μ Q)) := by
  have ht : ∀ j k, Tendsto (fun n => v12_tensorL1Class μ j k (Qn n)) atTop
      (𝓝 (v12_tensorL1Class μ j k Q)) :=
    fun j k => ((v12_tensorL1Class_continuous μ j k).tendsto Q).comp hQ
  have hs : ∀ j k, Tendsto (fun n => v12_S_L1Class μ j k (Qn n)) atTop
      (𝓝 (v12_S_L1Class μ j k Q)) := by
    intro j k
    exact (Complex.reCLM.compLpL 1 μ).continuous.tendsto _ |>.comp (ht j k)
  refine ⟨?_, hs, (hs 0 0).add (hs 1 1)⟩
  exact ((Complex.imCLM.compLpL 1 μ).continuous.tendsto _ |>.comp (ht 1 0)).const_smul (4 : ℝ)

theorem v12_B_L1Class_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : Lp V12Field 2 μ) :
    (v12_B_L1Class μ Q : Ω → ℝ) =ᵐ[μ]
      fun z => 4 * (star ((Q z) 0) * (Q z) 1).im := by
  filter_upwards [Lp.coeFn_smul (4 : ℝ)
      (Complex.imCLM.compLp (v12_tensorL1Class μ 1 0 Q)),
    Complex.imCLM.coeFn_compLp (v12_tensorL1Class μ 1 0 Q),
    v12_tensorL1Class_ae μ 1 0 Q] with z hsm him ht
  change v12_B_L1Class μ Q z = _
  change v12_B_L1Class μ Q z = 4 * (Complex.imCLM.compLp (v12_tensorL1Class μ 1 0 Q)) z at hsm
  change (Complex.imCLM.compLp (v12_tensorL1Class μ 1 0 Q)) z =
    (v12_tensorL1Class μ 1 0 Q z).im at him
  rw [hsm, him, ht]

theorem v12_S_L1Class_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (Q : Lp V12Field 2 μ) :
    (v12_S_L1Class μ j k Q : Ω → ℝ) =ᵐ[μ]
      fun z => (star ((Q z) k) * (Q z) j).re := by
  filter_upwards [Complex.reCLM.coeFn_compLp (v12_tensorL1Class μ j k Q),
    v12_tensorL1Class_ae μ j k Q] with z hre ht
  change v12_S_L1Class μ j k Q z = _
  change v12_S_L1Class μ j k Q z = (v12_tensorL1Class μ j k Q z).re at hre
  rw [hre, ht]

theorem v12_massL1Class_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : Lp V12Field 2 μ) :
    (v12_massL1Class μ Q : Ω → ℝ) =ᵐ[μ]
      fun z => ‖(Q z) 0‖ ^ 2 + ‖(Q z) 1‖ ^ 2 := by
  have hid (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    change (Complex.conj z * z).re = _
    rw [Complex.conj_mul']
    rfl
  filter_upwards [Lp.coeFn_add (v12_S_L1Class μ 0 0 Q) (v12_S_L1Class μ 1 1 Q),
    v12_S_L1Class_ae μ 0 0 Q, v12_S_L1Class_ae μ 1 1 Q] with z ha h0 h1
  change v12_massL1Class μ Q z = _
  change v12_massL1Class μ Q z = v12_S_L1Class μ 0 0 Q z + v12_S_L1Class μ 1 1 Q z at ha
  rw [ha, h0, h1, hid, hid]

noncomputable def v12_squareL1Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j : Fin 2)
    (Q : Lp V12Field 2 μ) : Lp ℂ 1 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holder 1 (v12_componentL2 μ j Q) (v12_componentL2 μ j Q)

noncomputable def v12_W_L1Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : Lp V12Field 2 μ) : Lp ℂ 1 μ :=
  (2 : ℂ) • (v12_squareL1Class μ 0 Q + v12_squareL1Class μ 1 Q)

theorem v12_squareL1Class_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j : Fin 2)
    (Q : Lp V12Field 2 μ) :
    (v12_squareL1Class μ j Q : Ω → ℂ) =ᵐ[μ] fun z => ((Q z) j) ^ 2 := by
  have hj := (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL Q
  have hp := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 1)
    (v12_componentL2 μ j Q) (v12_componentL2 μ j Q)
  filter_upwards [hj, hp] with z hzj hzp
  change v12_componentL2 μ j Q z = (Q z) j at hzj
  change v12_squareL1Class μ j Q z = v12_componentL2 μ j Q z * v12_componentL2 μ j Q z at hzp
  change v12_squareL1Class μ j Q z = _
  rw [hzp, hzj, pow_two]

theorem v12_W_L1Class_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : Lp V12Field 2 μ) :
    (v12_W_L1Class μ Q : Ω → ℂ) =ᵐ[μ]
      fun z => 2 * (((Q z) 0) ^ 2 + ((Q z) 1) ^ 2) := by
  filter_upwards [Lp.coeFn_smul (2 : ℂ)
      (v12_squareL1Class μ 0 Q + v12_squareL1Class μ 1 Q),
    Lp.coeFn_add (v12_squareL1Class μ 0 Q) (v12_squareL1Class μ 1 Q),
    v12_squareL1Class_ae μ 0 Q, v12_squareL1Class_ae μ 1 Q] with z hsm ha h0 h1
  change v12_W_L1Class μ Q z = _
  change v12_W_L1Class μ Q z = 2 * (v12_squareL1Class μ 0 Q + v12_squareL1Class μ 1 Q) z at hsm
  rw [hsm, ha, h0, h1]

theorem v12_W_strong_L1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Qn : ℕ → Lp V12Field 2 μ) (Q : Lp V12Field 2 μ)
    (hQ : Tendsto Qn atTop (𝓝 Q)) :
    Tendsto (fun n => v12_W_L1Class μ (Qn n)) atTop (𝓝 (v12_W_L1Class μ Q)) := by
  have hs : ∀ j, Continuous (v12_squareL1Class μ j) := by
    intro j
    have h := ((ContinuousLinearMap.mul ℂ ℂ).holderL μ 2 2 1).continuous₂.comp
      ((v12_componentL2 μ j).continuous.prodMk (v12_componentL2 μ j).continuous)
    simpa only [Function.comp_def, Function.uncurry, ContinuousLinearMap.holderL_apply_apply,
      v12_squareL1Class] using h
  exact (((hs 0).tendsto Q |>.comp hQ).add ((hs 1).tendsto Q |>.comp hQ)).const_smul (2 : ℂ)

#print axioms v12_squareL1Class_ae
#print axioms v12_W_L1Class_ae
#print axioms v12_W_strong_L1

#print axioms v12_B_L1Class_ae
#print axioms v12_S_L1Class_ae
#print axioms v12_massL1Class_ae

#print axioms v12_tensorL1Class_ae
#print axioms v12_tensorL1Class_continuous
#print axioms v12_quadratic_coefficients_strong_L1
end SMScattering.W20Full
