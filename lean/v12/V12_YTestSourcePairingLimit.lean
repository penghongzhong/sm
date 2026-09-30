import lean.v12.V12_WeakTimeIntegration
import lean.v12.V12_TestCutoffApproximation

/-!
W20 Theorem 7.2: transfer spatial kernel convergence to actual time-L1
source convergence. The bilinear maps are the existing L2-L2 and L4-L43
integral pairings. Spatial testing has signs i, -2, -i.
No time-L1 convergence is an input to the source-limit theorem. Spatial
kernel convergence and the same time-valued Q,F,G are explicit inputs.
The original PDE residual, derivative-kernel approximation and same-field
Hodge/source realization remain separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

section Pairing

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Quantitative time-L1 error for an actual continuous bilinear pairing. -/
theorem v12_pairing_norm_L1_le
    (μ : Measure ℝ) (B : E →L[ℂ] F →L[ℂ] H)
    (u v : E) (f : ℝ → F) (hf : Integrable f μ) :
    (∫ t, ‖B u (f t) - B v (f t)‖ ∂μ) ≤
      ‖B‖ * ‖u - v‖ * (∫ t, ‖f t‖ ∂μ) := by
  have hi : Integrable (fun t => ‖B u (f t) - B v (f t)‖) μ :=
    ((B u).integrable_comp hf |>.sub ((B v).integrable_comp hf)).norm
  calc
    (∫ t, ‖B u (f t) - B v (f t)‖ ∂μ)
        ≤ ∫ t, (‖B‖ * ‖u - v‖) * ‖f t‖ ∂μ := by
      apply integral_mono_ae hi (hf.norm.const_mul _)
      apply Filter.Eventually.of_forall
      intro t
      change ‖B u (f t) - B v (f t)‖ ≤ (‖B‖ * ‖u - v‖) * ‖f t‖
      have heq : B u (f t) - B v (f t) = B (u - v) (f t) := by
        simp only [map_sub, sub_apply]
      rw [heq]
      exact ((B (u - v)).le_opNorm (f t)).trans
        (mul_le_mul_of_nonneg_right (B.le_opNorm (u - v)) (norm_nonneg _))
    _ = ‖B‖ * ‖u - v‖ * (∫ t, ‖f t‖ ∂μ) := integral_const_mul _ _

/-- Norm convergence of the spatial kernel implies norm-L1 convergence of
its pairing with the same time-integrable source. -/
theorem v12_pairing_norm_L1_tendsto
    (μ : Measure ℝ) (B : E →L[ℂ] F →L[ℂ] H)
    (kR : ℕ → E) (k : E) (hk : Tendsto kR atTop (𝓝 k))
    (f : ℝ → F) (hf : Integrable f μ) :
    Tendsto (fun R => ∫ t, ‖B (kR R) (f t) - B k (f t)‖ ∂μ)
      atTop (𝓝 0) := by
  have hn : Tendsto (fun R => ‖kR R - k‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hk.sub_const k).norm
  have hlim : Tendsto
      (fun R => ‖B‖ * ‖kR R - k‖ * (∫ t, ‖f t‖ ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hn.const_mul ‖B‖).mul_const (∫ t, ‖f t‖ ∂μ)
  exact squeeze_zero
    (fun R => integral_nonneg (fun t => norm_nonneg _))
    (fun R => v12_pairing_norm_L1_le μ B (kR R) k f hf) hlim

end Pairing

/-- Finite-source assembly at the level of actual Bochner norm integrals. -/
theorem v12_norm_L1_add_tendsto
    {H : Type*} [NormedAddCommGroup H]
    (μ : Measure ℝ) (uR vR : ℕ → ℝ → H) (u v : ℝ → H)
    (huR : ∀ R, Integrable (uR R) μ) (hvR : ∀ R, Integrable (vR R) μ)
    (hu : Integrable u μ) (hv : Integrable v μ)
    (hU : Tendsto (fun R => ∫ t, ‖uR R t - u t‖ ∂μ) atTop (𝓝 0))
    (hV : Tendsto (fun R => ∫ t, ‖vR R t - v t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto
      (fun R => ∫ t, ‖(uR R t + vR R t) - (u t + v t)‖ ∂μ)
      atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun R => (∫ t, ‖uR R t - u t‖ ∂μ) + (∫ t, ‖vR R t - v t‖ ∂μ))
      atTop (𝓝 0) := by simpa only [add_zero] using hU.add hV
  apply squeeze_zero (fun R => integral_nonneg (fun t => norm_nonneg _)) _ hlim
  intro R
  calc
    _ ≤ ∫ t, (‖uR R t - u t‖ + ‖vR R t - v t‖) ∂μ := by
      apply integral_mono_ae
        (((huR R).add (hvR R)).sub (hu.add hv)).norm
        (((huR R).sub hu).norm.add ((hvR R).sub hv).norm)
      apply Filter.Eventually.of_forall
      intro t
      rw [add_sub_add_comm]
      exact norm_add_le _ _
    _ = _ := integral_add ((huR R).sub hu).norm ((hvR R).sub hv).norm

/-- The signs are fixed by the spatial weak-PDE test, not chosen by a bound. -/
noncomputable def v12_testLaplacianPairing :
    V12ScalarL2 →L[ℂ] V12SpatialL2 →L[ℂ] V12Field :=
  (Complex.I : ℂ) • v12_L2ConvolutionPairing

noncomputable def v12_testGradientPairing :
    V12ScalarL2 →L[ℂ] V12SpatialL2 →L[ℂ] V12Field :=
  (-2 : ℂ) • v12_L2ConvolutionPairing

noncomputable def v12_testZeroOrderPairing :
    V12ScalarL4 →L[ℂ] V12SpatialLFourThirds →L[ℂ] V12Field :=
  (-Complex.I : ℂ) • v12_L4L43ConvolutionPairing

/-- At fixed x, d is the L2 class of Delta_y psi, b_j of partial_yj psi,
and k the L4 class of psi. The limiting b_j equals -partial_j K(x-·).
Fin 2 coordinates 0,1 correspond to manuscript coordinates 1,2. -/
noncomputable def v12_testSourceFromLpKernels
    (d : V12ScalarL2) (b : Fin 2 → V12ScalarL2) (k : V12ScalarL4)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds) (t : ℝ) : V12Field :=
  v12_testLaplacianPairing d (Q t) +
    v12_testGradientPairing (b 0) (F 0 t) +
    v12_testGradientPairing (b 1) (F 1 t) +
    v12_testZeroOrderPairing k (G t)

theorem v12_testSourceFromLpKernels_integrable
    (μ : Measure ℝ)
    (d : V12ScalarL2) (b : Fin 2 → V12ScalarL2) (k : V12ScalarL4)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : Integrable Q μ) (hF : ∀ j, Integrable (F j) μ) (hG : Integrable G μ) :
    Integrable (v12_testSourceFromLpKernels d b k Q F G) μ := by
  exact (((v12_testLaplacianPairing d).integrable_comp hQ).add
      ((v12_testGradientPairing (b 0)).integrable_comp (hF 0))).add
      ((v12_testGradientPairing (b 1)).integrable_comp (hF 1)) |>.add
      ((v12_testZeroOrderPairing k).integrable_comp hG)

/-- The time-L1 source limit is proved from spatial L2/L4 limits. -/
theorem v12_testSourceFromLpKernels_L1_tendsto
    (μ : Measure ℝ)
    (dR : ℕ → V12ScalarL2) (bR : ℕ → Fin 2 → V12ScalarL2)
    (kR : ℕ → V12ScalarL4)
    (d : V12ScalarL2) (b : Fin 2 → V12ScalarL2) (k : V12ScalarL4)
    (hd : Tendsto dR atTop (𝓝 d))
    (hb : ∀ j, Tendsto (fun R => bR R j) atTop (𝓝 (b j)))
    (hk : Tendsto kR atTop (𝓝 k))
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : Integrable Q μ) (hF : ∀ j, Integrable (F j) μ) (hG : Integrable G μ) :
    Tendsto
      (fun R => ∫ t, ‖v12_testSourceFromLpKernels (dR R) (bR R) (kR R) Q F G t -
        v12_testSourceFromLpKernels d b k Q F G t‖ ∂μ) atTop (𝓝 0) := by
  let U : ℕ → ℝ → V12Field := fun R t => v12_testLaplacianPairing (dR R) (Q t)
  let u : ℝ → V12Field := fun t => v12_testLaplacianPairing d (Q t)
  let V : Fin 2 → ℕ → ℝ → V12Field := fun j R t =>
    v12_testGradientPairing (bR R j) (F j t)
  let v : Fin 2 → ℝ → V12Field := fun j t => v12_testGradientPairing (b j) (F j t)
  let W : ℕ → ℝ → V12Field := fun R t => v12_testZeroOrderPairing (kR R) (G t)
  let w : ℝ → V12Field := fun t => v12_testZeroOrderPairing k (G t)
  have hUi : ∀ R, Integrable (U R) μ :=
    fun R => (v12_testLaplacianPairing (dR R)).integrable_comp hQ
  have hui : Integrable u μ := (v12_testLaplacianPairing d).integrable_comp hQ
  have hVi : ∀ j R, Integrable (V j R) μ :=
    fun j R => (v12_testGradientPairing (bR R j)).integrable_comp (hF j)
  have hvi : ∀ j, Integrable (v j) μ :=
    fun j => (v12_testGradientPairing (b j)).integrable_comp (hF j)
  have hWi : ∀ R, Integrable (W R) μ :=
    fun R => (v12_testZeroOrderPairing (kR R)).integrable_comp hG
  have hwi : Integrable w μ := (v12_testZeroOrderPairing k).integrable_comp hG
  have hU := v12_pairing_norm_L1_tendsto μ v12_testLaplacianPairing dR d hd Q hQ
  have hV₀ := v12_pairing_norm_L1_tendsto μ v12_testGradientPairing
    (fun R => bR R 0) (b 0) (hb 0) (F 0) (hF 0)
  have hV₁ := v12_pairing_norm_L1_tendsto μ v12_testGradientPairing
    (fun R => bR R 1) (b 1) (hb 1) (F 1) (hF 1)
  have hW := v12_pairing_norm_L1_tendsto μ v12_testZeroOrderPairing kR k hk G hG
  have h01 := v12_norm_L1_add_tendsto μ U (V 0) u (v 0)
    hUi (hVi 0) hui (hvi 0) hU hV₀
  have h012 := v12_norm_L1_add_tendsto μ
    (fun R t => U R t + V 0 R t) (V 1) (fun t => u t + v 0 t) (v 1)
    (fun R => (hUi R).add (hVi 0 R)) (hVi 1) (hui.add (hvi 0)) (hvi 1) h01 hV₁
  exact v12_norm_L1_add_tendsto μ
    (fun R t => U R t + V 0 R t + V 1 R t) W (fun t => u t + v 0 t + v 1 t) w
    (fun R => ((hUi R).add (hVi 0 R)).add (hVi 1 R)) hWi
    ((hui.add (hvi 0)).add (hvi 1)) hwi h012 hW

/-- Precisely Linfty_t L2_x, L2_t L2_x and L43_t L43_x on finite time measure. -/
theorem v12_testSourceFromLpKernels_L1_tendsto_of_MemLp
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (dR : ℕ → V12ScalarL2) (bR : ℕ → Fin 2 → V12ScalarL2)
    (kR : ℕ → V12ScalarL4)
    (d : V12ScalarL2) (b : Fin 2 → V12ScalarL2) (k : V12ScalarL4)
    (hd : Tendsto dR atTop (𝓝 d))
    (hb : ∀ j, Tendsto (fun R => bR R j) atTop (𝓝 (b j)))
    (hk : Tendsto kR atTop (𝓝 k))
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : MemLp Q ∞ μ) (hF : ∀ j, MemLp (F j) 2 μ)
    (hG : MemLp G ((4 : ℝ≥0∞) / 3) μ) :
    Tendsto
      (fun R => ∫ t, ‖v12_testSourceFromLpKernels (dR R) (bR R) (kR R) Q F G t -
        v12_testSourceFromLpKernels d b k Q F G t‖ ∂μ) atTop (𝓝 0) := by
  exact v12_testSourceFromLpKernels_L1_tendsto μ dR bR kR d b k hd hb hk Q F G
    (memLp_one_iff_integrable.mp (hQ.mono_exponent le_top))
    (fun j => memLp_one_iff_integrable.mp ((hF j).mono_exponent (by norm_num)))
    (memLp_one_iff_integrable.mp (hG.mono_exponent v12_one_le_fourThirds_ENNReal))

/-- Separate kernel-checked representative substitution avoids unfolding the
entire convolution-to-BCF construction inside a limit proof. -/
theorem v12_schwartzL2_convolutionRep_integral
    (k : SchwartzMap V12Spatial ℂ) (f : V12SpatialL2) (x : V12Spatial) :
    v12_L2ConvolutionRep (k.toLp 2 (volume : Measure V12Spatial)) f x =
      ∫ y : V12Spatial, k (x-y) • f y := by
  rw [v12_L2ConvolutionRep_eq_integral]
  apply integral_congr_ae
  have hk := (v12_subLeft_measurePreserving x).quasiMeasurePreserving.ae
    (k.coeFn_toLp 2 (volume : Measure V12Spatial))
  filter_upwards [hk] with y hy
  have hy' : (k.toLp 2 (volume : Measure V12Spatial) : V12Spatial → ℂ) (x-y) =
      k (x-y) := by
    simpa only [v12_subLeftFamily_apply] using hy
  exact congrArg (fun z : ℂ => z • f y) hy'

/-- Concrete compact tests converge to the actual BCF convolution value. -/
theorem v12_compactSpatialTest_endpoint_to_BCF
    (χ : V12Spatial → ℝ) (hχc : Continuous χ) (hχ0 : χ 0 = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial) (f : V12SpatialL2) :
    Tendsto (fun R => ∫ y, v12_compactSpatialTest χ k R x y • f y)
      atTop (𝓝 (v12_L2ConvolutionBCFCLM (k.toLp 2 (volume : Measure V12Spatial)) f x)) := by
  simpa only [v12_L2ConvolutionBCFCLM_apply, v12_schwartzL2_convolutionRep_integral] using
    v12_compactSpatialTest_endpoint_tendsto χ hχc hχ0 hχb k x
      (fun y => f y) (Lp.memLp f)

#print axioms v12_pairing_norm_L1_le
#print axioms v12_pairing_norm_L1_tendsto
#print axioms v12_norm_L1_add_tendsto
#print axioms v12_testSourceFromLpKernels_integrable
#print axioms v12_testSourceFromLpKernels_L1_tendsto
#print axioms v12_testSourceFromLpKernels_L1_tendsto_of_MemLp
#print axioms v12_schwartzL2_convolutionRep_integral
#print axioms v12_compactSpatialTest_endpoint_to_BCF

end SMScattering.W20Full
