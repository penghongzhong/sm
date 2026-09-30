import lean.v12.V12_SourceProducts

/-! The actual xi_j xi_l / |xi|² multiplier in A0, as a bounded spatial
L2 operator. This does not assume a Riesz-transform budget. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open Filter MeasureTheory FourierTransform
open scoped Topology ENNReal

noncomputable def v12_coulombRieszSymbol (j l : Fin 2) (ξ : V12Spatial) : ℂ :=
  ((ξ j * ξ l / ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem v12_coulombRieszSymbol_measurable (j l : Fin 2) :
    Measurable (v12_coulombRieszSymbol j l) := by
  have hj : Continuous (fun ξ : V12Spatial => ξ j) := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  have hl : Continuous (fun ξ : V12Spatial => ξ l) := (EuclideanSpace.proj (𝕜 := ℝ) l).continuous
  unfold v12_coulombRieszSymbol
  fun_prop

theorem v12_coulombRieszSymbol_bound (j l : Fin 2) (ξ : V12Spatial) :
    ‖v12_coulombRieszSymbol j l ξ‖ ≤ 1 := by
  by_cases hz : ‖ξ‖ = 0
  · simp [v12_coulombRieszSymbol, hz]
  · have hp : 0 < ‖ξ‖ ^ 2 := sq_pos_of_ne_zero hz
    rw [v12_coulombRieszSymbol, Complex.norm_real, norm_div, norm_mul,
      Real.norm_of_nonneg (sq_nonneg _)]
    apply (div_le_one hp).mpr
    simpa only [pow_two] using mul_le_mul (PiLp.norm_apply_le ξ j) (PiLp.norm_apply_le ξ l)
      (norm_nonneg _) (norm_nonneg _)

theorem v12_coulombRieszSymbol_memLp (j l : Fin 2) :
    MemLp (v12_coulombRieszSymbol j l) ∞ (volume : Measure V12Spatial) :=
  memLp_top_of_bound (v12_coulombRieszSymbol_measurable j l).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (v12_coulombRieszSymbol_bound j l))

noncomputable def v12_coulombRieszSymbolClass (j l : Fin 2) : V12SymbolLInf :=
  (v12_coulombRieszSymbol_memLp j l).toLp (v12_coulombRieszSymbol j l)

theorem v12_coulombRieszSymbolClass_norm (j l : Fin 2) :
    ‖v12_coulombRieszSymbolClass j l‖ ≤ 1 := by
  have h := eLpNormEssSup_le_of_ae_bound
    (μ := (volume : Measure V12Spatial))
    (Filter.Eventually.of_forall (v12_coulombRieszSymbol_bound j l))
  rw [← eLpNorm_exponent_top (v12_coulombRieszSymbol_measurable j l).aestronglyMeasurable] at h
  have hr := ENNReal.toReal_mono (by norm_num : ENNReal.ofReal (1 : ℝ) ≠ ∞) h
  simpa [v12_coulombRieszSymbolClass, Lp.norm_toLp] using hr

noncomputable def v12_scalarL2Multiplier (m : V12SymbolLInf) : V12ScalarL2 →L[ℂ] V12ScalarL2 :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).holderL volume ∞ 2 2) m

theorem v12_scalarL2Multiplier_bound (m : V12SymbolLInf) (f : V12ScalarL2) :
    ‖v12_scalarL2Multiplier m f‖ ≤ ‖m‖ * ‖f‖ := by
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.lsmul ℂ ℂ
  have h := B.norm_holder_apply_apply_le (r := 2) m f
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
  change ‖B.holder 2 m f‖ ≤ _
  apply h.trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hB (norm_nonneg m)) (norm_nonneg f)

noncomputable def v12_coulombRieszOperator (j l : Fin 2) : V12ScalarL2 →L[ℂ] V12ScalarL2 :=
  fourierInvCLM ℂ V12ScalarL2 ∘L
    v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j l) ∘L fourierCLM ℂ V12ScalarL2

theorem v12_coulombRieszOperator_bound (j l : Fin 2) (f : V12ScalarL2) :
    ‖v12_coulombRieszOperator j l f‖ ≤ ‖f‖ := by
  change ‖𝓕⁻ (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j l) (𝓕 f))‖ ≤ ‖f‖
  have hi (g : V12ScalarL2) : ‖𝓕⁻ g‖ = ‖g‖ := by
    calc
      ‖𝓕⁻ g‖ = ‖𝓕 (𝓕⁻ g)‖ := (Lp.norm_fourier_eq _).symm
      _ = ‖g‖ := by rw [fourier_fourierInv_eq]
  rw [hi]
  exact (v12_scalarL2Multiplier_bound _ _).trans
    (by simpa only [Lp.norm_fourier_eq, one_mul] using
      mul_le_mul_of_nonneg_right (v12_coulombRieszSymbolClass_norm j l) (norm_nonneg (𝓕 f)))


theorem v12_coulombRieszOperator_weak_limit
    (j l : Fin 2) (fn : ℕ → V12ScalarL2) (f : V12ScalarL2)
    (hw : ∀ φ : V12ScalarL2 →L[ℂ] ℂ,
      Tendsto (fun n => φ (fn n)) atTop (𝓝 (φ f))) :
    ∀ φ : V12ScalarL2 →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_coulombRieszOperator j l (fn n))) atTop
        (𝓝 (φ (v12_coulombRieszOperator j l f))) := by
  intro φ
  exact hw (φ.comp (v12_coulombRieszOperator j l))

noncomputable def v12_temporalCoulombClass
    (S : Fin 2 → Fin 2 → V12ScalarL2) (m : V12ScalarL2) : V12ScalarL2 :=
  (4 : ℂ) • (∑ j, ∑ l, v12_coulombRieszOperator j l (S j l)) - (2 : ℂ) • m

theorem v12_temporalCoulombClass_bound
    (S : Fin 2 → Fin 2 → V12ScalarL2) (m : V12ScalarL2) :
    ‖v12_temporalCoulombClass S m‖ ≤ 4 * (∑ j, ∑ l, ‖S j l‖) + 2 * ‖m‖ := by
  unfold v12_temporalCoulombClass
  have hs : ‖∑ j, ∑ l, v12_coulombRieszOperator j l (S j l)‖ ≤ ∑ j, ∑ l, ‖S j l‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l hl
    exact v12_coulombRieszOperator_bound j l (S j l)
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, Complex.norm_ofNat]
  exact add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) le_rfl

#print axioms v12_coulombRieszOperator_weak_limit
#print axioms v12_temporalCoulombClass_bound
#print axioms v12_coulombRieszSymbol_bound
#print axioms v12_coulombRieszSymbolClass_norm
#print axioms v12_coulombRieszOperator_bound
end SMScattering.W20Full
