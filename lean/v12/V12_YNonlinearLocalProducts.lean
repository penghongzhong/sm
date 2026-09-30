import lean.v12.V12_SourceProducts
import Mathlib.MeasureTheory.Function.Holder

/-!
Actual L2 x L2 -> L1 drift products and strong convergence on the cylinder
measure. This is an infinite-dimensional function-space statement; no product
convergence is a hypothesis. Obtaining the strong L2 Hodge-potential limit
from the original Q sequence is a separate, still-open obligation.
-/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_driftL1Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Lp ℂ 2 μ) (Q : Lp V12Field 2 μ) : Lp V12Field 1 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] V12Field →L[ℂ] V12Field).holder 1 A Q

theorem v12_driftL1Class_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Lp ℂ 2 μ) (Q : Lp V12Field 2 μ) :
    (v12_driftL1Class μ A Q : Ω → V12Field) =ᵐ[μ] fun z => A z • Q z :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] V12Field →L[ℂ] V12Field).coeFn_holder A Q

theorem v12_strong_L2_drift_product_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (An : ℕ → Lp ℂ 2 μ) (Qn : ℕ → Lp V12Field 2 μ)
    (A : Lp ℂ 2 μ) (Q : Lp V12Field 2 μ)
    (hA : Tendsto An atTop (𝓝 A)) (hQ : Tendsto Qn atTop (𝓝 Q)) :
    Tendsto (fun n => v12_driftL1Class μ (An n) (Qn n)) atTop
      (𝓝 (v12_driftL1Class μ A Q)) := by
  let B : ℂ →L[ℂ] V12Field →L[ℂ] V12Field := ContinuousLinearMap.lsmul ℂ ℂ
  exact ((B.holderL μ 2 2 1).continuous₂.tendsto (A,Q)).comp (hA.prodMk_nhds hQ)

/-- The same constructed L1 class agrees with the actual raw product. -/
theorem v12_driftL1Class_raw_rep
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Lp ℂ 2 μ) (Q : Lp V12Field 2 μ)
    (a : Ω → ℂ) (q : Ω → V12Field)
    (hA : (A : Ω → ℂ) =ᵐ[μ] a) (hQ : (Q : Ω → V12Field) =ᵐ[μ] q) :
    (v12_driftL1Class μ A Q : Ω → V12Field) =ᵐ[μ] fun z => a z • q z := by
  filter_upwards [v12_driftL1Class_ae μ A Q, hA, hQ] with z hz ha hq
  rw [hz, ha, hq]

#print axioms v12_driftL1Class_ae
#print axioms v12_driftL1Class_raw_rep
#print axioms v12_strong_L2_drift_product_limit
end SMScattering.W20Full
