import lean.v12.V12_YMeasurableLocalLimitGluing

/-! Countable exhaustion gives the actual all-real-radius local conclusions.
The norm convergence transfer includes a finite-norm hypothesis, so `toReal`
cannot hide an infinite norm. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

def v12_real_spatial_cylinder (r : ℝ) : Set V12Spacetime :=
  {z | ‖z.2‖ < r}

theorem v12_real_cylinder_subset (r : ℝ) :
    ∃ R : ℕ, v12_real_spatial_cylinder r ⊆ v12_spatial_cylinder R := by
  obtain ⟨R, hR⟩ := exists_nat_gt r
  refine ⟨R, ?_⟩
  intro z hz
  exact hz.trans (hR.trans (lt_add_one _))

theorem v12_local_memLp_all_real_radii
    {E : Type} [NormedAddCommGroup E]
    (a b : ℝ) (f : V12Spacetime → E) (p : ℝ≥0∞)
    (hf : ∀ R, MemLp f p ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (r : ℝ) : MemLp f p ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)) := by
  obtain ⟨R, hR⟩ := v12_real_cylinder_subset r
  exact MemLp.mono_measure (Measure.restrict_mono hR le_rfl) (hf R)

theorem v12_local_eLpNorm_limit_all_real_radii
    {E : Type} [NormedAddCommGroup E]
    (a b : ℝ) (f : ℕ → V12Spacetime → E) (p : ℝ≥0∞)
    (hf : ∀ R n, MemLp (f n) p ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (f n) p
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (r : ℝ) : Tendsto (fun n => (eLpNorm (f n) p
      ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := v12_real_cylinder_subset r
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ (hlim R)
  intro n
  exact ENNReal.toReal_mono (hf R n).eLpNorm_ne_top
    (eLpNorm_mono_measure (f n) (Measure.restrict_mono hR le_rfl))

#print axioms v12_local_memLp_all_real_radii
#print axioms v12_local_eLpNorm_limit_all_real_radii
end SMScattering.W20Full
