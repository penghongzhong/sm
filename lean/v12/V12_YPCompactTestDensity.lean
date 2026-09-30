import lean.v12.V12_SourceProducts
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! The concrete compact continuous L2 tests used in nonlinear weak closure
are dense for the actual spacetime measure. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_compactContinuousTests (μ : Measure V12Spacetime) :
    Set (Lp ℂ 2 μ) :=
  {φ | ∃ g : V12Spacetime → ℂ, HasCompactSupport g ∧ Continuous g ∧
    ∃ hg : MemLp g 2 μ, φ = hg.toLp g}

theorem v12_compactContinuousTests_dense (μ : Measure V12Spacetime) [μ.Regular] :
    Dense (v12_compactContinuousTests μ) := by
  intro φ
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  obtain ⟨g, hgcompact, hgnorm, hgcont, hgm⟩ :=
    (Lp.memLp φ).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hε.ne'
  refine ⟨hgm.toLp g, ⟨g, hgcompact, hgcont, hgm, rfl⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn φ (Lp.memLp φ), Lp.edist_toLp_toLp]

theorem v12_slab_measure_regular (a b : ℝ) : (v12_slab_measure a b).Regular := by
  unfold v12_slab_measure
  infer_instance

theorem v12_slab_compactContinuousTests_dense (a b : ℝ) :
    Dense (v12_compactContinuousTests (v12_slab_measure a b)) := by
  letI := v12_slab_measure_regular a b
  exact v12_compactContinuousTests_dense _

#print axioms v12_compactContinuousTests_dense
#print axioms v12_slab_measure_regular
#print axioms v12_slab_compactContinuousTests_dense
end SMScattering.W20Full
