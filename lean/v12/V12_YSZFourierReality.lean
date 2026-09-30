import lean.v12.V12_YSCoulombRieszTimeOperator

/-! Real-output correspondence for the actual real even Riesz symbol.
Fourier conjugation/reflection identities are derived through Schwartz density,
not introduced as an external interface. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace SMScattering.W20Full
open MeasureTheory FourierTransform
open scoped ENNReal RealInnerProductSpace

noncomputable def v12_L2Conj : V12ScalarL2 →L[ℝ] V12ScalarL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

noncomputable def v12_L2Reflect : V12ScalarL2 →ₗᵢ[ℂ] V12ScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : V12Spatial => -x)
    (LinearIsometryEquiv.neg ℝ (E := V12Spatial)).measurePreserving

theorem v12_L2Conj_ae (f : V12ScalarL2) :
    (v12_L2Conj f : V12Spatial → ℂ) =ᵐ[volume] fun x => star (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

theorem v12_L2Conj_involutive (f : V12ScalarL2) : v12_L2Conj (v12_L2Conj f) = f := by
  apply Lp.ext_iff.mpr
  filter_upwards [v12_L2Conj_ae (v12_L2Conj f), v12_L2Conj_ae f] with x hc hf
  simp only [hc, hf, star_star]

theorem v12_L2Reflect_ae (f : V12ScalarL2) :
    (v12_L2Reflect f : V12Spatial → ℂ) =ᵐ[volume] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (LinearIsometryEquiv.neg ℝ (E := V12Spatial)).measurePreserving

noncomputable def v12_schwartzConj (f : SchwartzMap V12Spatial ℂ) : SchwartzMap V12Spatial ℂ :=
  f.postcompCLM Complex.conjCLE.toContinuousLinearMap

noncomputable def v12_schwartzReflect (f : SchwartzMap V12Spatial ℂ) : SchwartzMap V12Spatial ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V12Spatial)) f

theorem v12_schwartzConj_toLp (f : SchwartzMap V12Spatial ℂ) :
    (v12_schwartzConj f).toLp 2 = v12_L2Conj (f.toLp 2) := by
  apply Lp.ext_iff.mpr
  filter_upwards [(v12_schwartzConj f).coeFn_toLp 2, v12_L2Conj_ae (f.toLp 2), f.coeFn_toLp 2]
    with x hcf hc hf
  rw [hcf, hc, hf]
  rfl

theorem v12_schwartzReflect_toLp (f : SchwartzMap V12Spatial ℂ) :
    (v12_schwartzReflect f).toLp 2 = v12_L2Reflect (f.toLp 2) := by
  apply Lp.ext_iff.mpr
  have hneg := (LinearIsometryEquiv.neg ℝ (E := V12Spatial)).measurePreserving
  filter_upwards [(v12_schwartzReflect f).coeFn_toLp 2, v12_L2Reflect_ae (f.toLp 2),
    hneg.quasiMeasurePreserving.ae (p := fun x : V12Spatial => (f.toLp 2 : V12Spatial → ℂ) x = f x) (f.coeFn_toLp 2 volume)] with x hr hn hf
  rw [hr, hn]
  exact hf.symm

theorem v12_raw_fourier_conj (f : V12Spatial → ℂ) (ξ : V12Spatial) :
    𝓕 (fun x => star (f x)) ξ = star (𝓕⁻ f ξ) := by
  rw [Real.fourier_eq', Real.fourierInv_eq', Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.star_def]
  congr 1
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem v12_schwartz_fourier_conj (f : SchwartzMap V12Spatial ℂ) :
    𝓕 (v12_schwartzConj f) = v12_schwartzConj (𝓕⁻ f) := by
  ext ξ
  simpa only [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe,
    v12_schwartzConj, SchwartzMap.postcompCLM_apply] using v12_raw_fourier_conj f ξ

theorem v12_L2_fourier_conj (f : V12ScalarL2) :
    𝓕 (v12_L2Conj f) = v12_L2Conj (𝓕⁻ f) := by
  apply DenseRange.induction_on (p := fun g : V12ScalarL2 =>
    𝓕 (v12_L2Conj g) = v12_L2Conj (𝓕⁻ g))
    (SchwartzMap.denseRange_toLpCLM (E := V12Spatial) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((fourierCLM ℂ V12ScalarL2).continuous.comp v12_L2Conj.continuous)
      (v12_L2Conj.continuous.comp (fourierInvCLM ℂ V12ScalarL2).continuous)
  intro g
  change 𝓕 (v12_L2Conj (g.toLp 2)) = v12_L2Conj (𝓕⁻ (g.toLp 2))
  rw [← v12_schwartzConj_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourierInv_eq, ← v12_schwartzConj_toLp, v12_schwartz_fourier_conj]

theorem v12_L2_conj_fourier (f : V12ScalarL2) :
    v12_L2Conj (𝓕 f) = 𝓕⁻ (v12_L2Conj f) := by
  have h := congrArg v12_L2Conj (v12_L2_fourier_conj (v12_L2Conj f))
  simpa only [v12_L2Conj_involutive] using h

theorem v12_schwartz_reflect_fourier (f : SchwartzMap V12Spatial ℂ) :
    v12_schwartzReflect (𝓕 f) = 𝓕⁻ f := by
  ext ξ
  simpa only [v12_schwartzReflect, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    LinearIsometryEquiv.neg_apply, SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe] using
    (Real.fourierInv_eq_fourier_neg f ξ).symm

theorem v12_L2_reflect_fourier (f : V12ScalarL2) : v12_L2Reflect (𝓕 f) = 𝓕⁻ f := by
  apply DenseRange.induction_on (p := fun g : V12ScalarL2 => v12_L2Reflect (𝓕 g) = 𝓕⁻ g)
    (SchwartzMap.denseRange_toLpCLM (E := V12Spatial) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (v12_L2Reflect.continuous.comp (fourierCLM ℂ V12ScalarL2).continuous)
      (fourierInvCLM ℂ V12ScalarL2).continuous
  intro g
  change v12_L2Reflect (𝓕 (g.toLp 2)) = 𝓕⁻ (g.toLp 2)
  rw [SchwartzMap.toLp_fourier_eq, ← v12_schwartzReflect_toLp,
    SchwartzMap.toLp_fourierInv_eq, v12_schwartz_reflect_fourier]

theorem v12_L2_fourier_reflect (f : V12ScalarL2) : 𝓕 (v12_L2Reflect f) = 𝓕⁻ f := by
  apply DenseRange.induction_on (p := fun g : V12ScalarL2 => 𝓕 (v12_L2Reflect g) = 𝓕⁻ g)
    (SchwartzMap.denseRange_toLpCLM (E := V12Spatial) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((fourierCLM ℂ V12ScalarL2).continuous.comp v12_L2Reflect.continuous)
      (fourierInvCLM ℂ V12ScalarL2).continuous
  intro g
  change 𝓕 (v12_L2Reflect (g.toLp 2)) = 𝓕⁻ (g.toLp 2)
  rw [← v12_schwartzReflect_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourierInv_eq]
  congr 1
  ext ξ
  simpa only [v12_schwartzReflect, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    LinearIsometryEquiv.neg_apply, SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe] using
    congrFun (Real.fourierInv_eq_fourier_comp_neg (g : V12Spatial → ℂ)).symm ξ

theorem v12_coulombMultiplier_ae (j k : Fin 2) (f : V12ScalarL2) :
    (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) f : V12Spatial → ℂ)
      =ᵐ[volume] fun ξ => v12_coulombRieszSymbol j k ξ * f ξ := by
  have hp := (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).coeFn_holder
    (r := 2) (v12_coulombRieszSymbolClass j k) f
  filter_upwards [hp, (v12_coulombRieszSymbol_memLp j k).coeFn_toLp] with ξ hξ hm
  change v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) f ξ =
    v12_coulombRieszSymbolClass j k ξ * f ξ at hξ
  change v12_coulombRieszSymbolClass j k ξ = v12_coulombRieszSymbol j k ξ at hm
  rw [hξ, hm]

theorem v12_coulombMultiplier_conj (j k : Fin 2) (f : V12ScalarL2) :
    v12_L2Conj (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) f) =
      v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) (v12_L2Conj f) := by
  apply Lp.ext_iff.mpr
  filter_upwards [v12_L2Conj_ae (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) f),
    v12_coulombMultiplier_ae j k f, v12_coulombMultiplier_ae j k (v12_L2Conj f),
    v12_L2Conj_ae f] with ξ hc hm hmc hcf
  rw [hc, hm, hmc, hcf]
  simp only [v12_coulombRieszSymbol, Complex.star_def, map_mul, Complex.conj_ofReal]

theorem v12_coulombMultiplier_reflect (j k : Fin 2) (f : V12ScalarL2) :
    v12_L2Reflect (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) f) =
      v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) (v12_L2Reflect f) := by
  apply Lp.ext_iff.mpr
  have hneg := (LinearIsometryEquiv.neg ℝ (E := V12Spatial)).measurePreserving
  filter_upwards [v12_L2Reflect_ae (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) f),
    hneg.quasiMeasurePreserving.ae (v12_coulombMultiplier_ae j k f),
    v12_coulombMultiplier_ae j k (v12_L2Reflect f), v12_L2Reflect_ae f] with ξ hn hm hmn hnf
  change v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) f (-ξ) =
    v12_coulombRieszSymbol j k (-ξ) * f (-ξ) at hm
  rw [hn, hm, hmn, hnf]
  congr 1
  simpa only [neg_one_smul] using v12_coulombRieszSymbol_scale j k (-1) (by norm_num) ξ

theorem v12_coulombRieszOperator_conj (j k : Fin 2) (f : V12ScalarL2) :
    v12_L2Conj (v12_coulombRieszOperator j k f) = v12_coulombRieszOperator j k (v12_L2Conj f) := by
  change v12_L2Conj (𝓕⁻ (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) (𝓕 f))) =
    𝓕⁻ (v12_scalarL2Multiplier (v12_coulombRieszSymbolClass j k) (𝓕 (v12_L2Conj f)))
  rw [← v12_L2_fourier_conj, v12_coulombMultiplier_conj, v12_L2_conj_fourier]
  rw [← v12_L2_reflect_fourier (v12_L2Conj f), ← v12_coulombMultiplier_reflect,
    v12_L2_fourier_reflect]

theorem v12_coulombRieszOperator_real (j k : Fin 2) (f : V12ScalarL2)
    (hf : ∀ᵐ x ∂(volume : Measure V12Spatial), star (f x) = f x) :
    ∀ᵐ x ∂(volume : Measure V12Spatial),
      star (v12_coulombRieszOperator j k f x) = v12_coulombRieszOperator j k f x := by
  have hc : v12_L2Conj f = f := Lp.ext_iff.mpr ((v12_L2Conj_ae f).trans hf)
  have h := v12_L2Conj_ae (v12_coulombRieszOperator j k f)
  rw [v12_coulombRieszOperator_conj, hc] at h
  exact h.symm

#print axioms v12_coulombRieszOperator_conj
#print axioms v12_coulombRieszOperator_real

#print axioms v12_L2_fourier_conj
#print axioms v12_L2_conj_fourier
#print axioms v12_L2_reflect_fourier
#print axioms v12_L2_fourier_reflect
end SMScattering.W20Full
