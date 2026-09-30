import lean.v12.V12_FrequencyTightnessLimit

/-! The degenerate finite interval is included without a positive-length hypothesis. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_zero_length_slab_measure (a : ℝ) : v12_slab_measure a a = 0 := by
  simp [v12_slab_measure, Set.Icc_self, Measure.restrict_singleton']

theorem v12_zero_length_common_limit (a : ℝ)
    (q : ℕ → ℝ → V12Spatial → V12Field) :
    ∃ (σ : ℕ → ℕ) (u : V12Spacetime → V12Field), StrictMono σ ∧
      StronglyMeasurable u ∧ ∀ R,
        MemLp u 2 ((v12_slab_measure a a).restrict (v12_spatial_cylinder R)) ∧
        (∀ n, MemLp (Function.uncurry (q (σ n))) 2
          ((v12_slab_measure a a).restrict (v12_spatial_cylinder R))) ∧
        Tendsto (fun n => (eLpNorm (fun z : V12Spacetime => q (σ n) z.1 z.2 - u z)
          2 ((v12_slab_measure a a).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
  refine ⟨id, 0, strictMono_id, stronglyMeasurable_zero, ?_⟩
  intro R
  simp only [v12_zero_length_slab_measure, Measure.restrict_zero,
    memLp_measure_zero, eLpNorm_measure_zero, ENNReal.toReal_zero, forall_const, true_and]
  exact tendsto_const_nhds

#print axioms v12_zero_length_slab_measure
#print axioms v12_zero_length_common_limit
end SMScattering.W20Full
