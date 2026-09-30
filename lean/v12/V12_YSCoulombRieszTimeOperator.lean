import lean.v12.V12_YRieszCoulombOperator

/-! Time lifting of the same spatial Fourier Riesz operator. Homogeneity
checks the 2pi Fourier-frequency normalization used in the manuscript. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_coulombRieszSymbol_scale (j l : Fin 2) (c : ℝ) (hc : c ≠ 0)
    (ξ : V12Spatial) : v12_coulombRieszSymbol j l (c • ξ) = v12_coulombRieszSymbol j l ξ := by
  by_cases hz : ‖ξ‖ = 0
  · have hξ : ξ = 0 := norm_eq_zero.mp hz
    simp [hξ, v12_coulombRieszSymbol]
  · unfold v12_coulombRieszSymbol
    congr 1
    simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hc, hz]
    <;> ring

theorem v12_coulombRieszSymbol_two_pi (j l : Fin 2) (ξ : V12Spatial) :
    v12_coulombRieszSymbol j l ((2 * Real.pi) • ξ) = v12_coulombRieszSymbol j l ξ :=
  v12_coulombRieszSymbol_scale j l (2 * Real.pi) (by positivity) ξ

theorem v12_coulombRieszOperator_opNorm (j l : Fin 2) :
    ‖v12_coulombRieszOperator j l‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [one_mul] using v12_coulombRieszOperator_bound j l f

noncomputable def v12_timeCoulombRieszOperator (μ : Measure ℝ) (j l : Fin 2) :
    Lp V12ScalarL2 2 μ →L[ℂ] Lp V12ScalarL2 2 μ :=
  (v12_coulombRieszOperator j l).compLpL 2 μ

theorem v12_timeCoulombRieszOperator_bound (μ : Measure ℝ) (j l : Fin 2) :
    ‖v12_timeCoulombRieszOperator μ j l‖ ≤ 1 :=
  ((v12_coulombRieszOperator j l).norm_compLpL_le (p := 2) (μ := μ)).trans
    (v12_coulombRieszOperator_opNorm j l)

theorem v12_timeCoulombRieszOperator_ae (μ : Measure ℝ) (j l : Fin 2)
    (f : Lp V12ScalarL2 2 μ) :
    (v12_timeCoulombRieszOperator μ j l f : ℝ → V12ScalarL2) =ᵐ[μ]
      fun t => v12_coulombRieszOperator j l (f t) :=
  (v12_coulombRieszOperator j l).coeFn_compLpL f

theorem v12_timeCoulombRieszOperator_weak_limit (μ : Measure ℝ) (j l : Fin 2)
    (fn : ℕ → Lp V12ScalarL2 2 μ) (f : Lp V12ScalarL2 2 μ)
    (hw : ∀ φ : Lp V12ScalarL2 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => φ (fn n)) atTop (𝓝 (φ f))) :
    ∀ φ : Lp V12ScalarL2 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_timeCoulombRieszOperator μ j l (fn n))) atTop
        (𝓝 (φ (v12_timeCoulombRieszOperator μ j l f))) := by
  intro φ
  exact hw (φ.comp (v12_timeCoulombRieszOperator μ j l))

#print axioms v12_coulombRieszSymbol_two_pi
#print axioms v12_timeCoulombRieszOperator_bound
#print axioms v12_timeCoulombRieszOperator_ae
#print axioms v12_timeCoulombRieszOperator_weak_limit
end SMScattering.W20Full
