import Mathlib

namespace SMScattering.W20Full

open MeasureTheory Filter
open scoped ENNReal Topology

/--
Finite-time L^∞_t L^2_x control implies membership in the product-space L^2.

The hypothesis hFiberBound is exactly the energy bound on almost every time
slice.  The proof is only Fubini/Tonelli plus integrability of a constant on a
finite measure space.
-/
theorem v12_memLp_two_of_fiber_energy
    {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure T) (ν : Measure X)
    [IsFiniteMeasure μ] [SFinite ν]
    (f : T × X → E)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (M : ℝ) (hM : 0 ≤ M)
    (hFiberIntegrable :
      ∀ᵐ t ∂μ, Integrable (fun x => ‖f (t, x)‖ ^ 2) ν)
    (hFiberBound :
      ∀ᵐ t ∂μ, (∫ x, ‖f (t, x)‖ ^ 2 ∂ν) ≤ M ^ 2) :
    MemLp f 2 (μ.prod ν) := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  let g : T × X → ℝ := fun z => ‖f z‖ ^ 2
  have hg : AEStronglyMeasurable g (μ.prod ν) := hf.norm.pow 2
  rw [integrable_prod_iff hg]
  refine ⟨hFiberIntegrable, ?_⟩
  have hOuterMeas :
      AEStronglyMeasurable
        (fun t => ∫ x, ‖g (t, x)‖ ∂ν) μ :=
    hg.norm.integral_prod_right'
  refine Integrable.mono'
    (integrable_const (M ^ 2)) hOuterMeas ?_
  filter_upwards [hFiberBound] with t ht
  have hnonneg :
      0 ≤ ∫ x, ‖g (t, x)‖ ∂ν :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => norm_nonneg (g (t, x)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    (∫ x, ‖g (t, x)‖ ∂ν)
        = ∫ x, ‖f (t, x)‖ ^ 2 ∂ν := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (t, x)‖)]
    _ ≤ M ^ 2 := ht

/-- The time-restricted Lebesgue measure used in the manuscript is finite. -/
noncomputable def v12_time_measure (a b : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Icc a b)

theorem v12_time_measure_finite (a b : ℝ) :
    IsFiniteMeasure (v12_time_measure a b) := by
  rw [MeasureTheory.isFiniteMeasure_restrict]
  exact (MeasureTheory.measure_Icc_lt_top).ne

#print axioms v12_memLp_two_of_fiber_energy
#print axioms v12_time_measure_finite

end SMScattering.W20Full
