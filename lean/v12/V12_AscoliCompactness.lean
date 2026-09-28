import Mathlib
import «lean.v12.V12_FrequencyTightnessLimit»

namespace SMScattering.W20Full

open Filter
open scoped Topology

theorem v12_ascoli_compact_closure
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (S : Set C(X, V12Field))
    (M : ℝ) (hM : 0 ≤ M)
    (hEq : Equicontinuous ((↑) : S → X → V12Field))
    (hBound : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ M) :
    IsCompact (closure S) := by
  let fam : Set (Set X) := {K | IsCompact K}
  have hfam : ∀ K ∈ fam, IsCompact K := by
    intro K hK
    exact hK
  have hclosed :
      IsClosedEmbedding
        (UniformOnFun.ofFun fam ∘
          (fun f : C(X, V12Field) => (f : X → V12Field))) := by
    simpa [fam, ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
      (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
        (α := X) (β := V12Field)).isClosedEmbedding
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := fam)
    (F := fun f : C(X, V12Field) => (f : X → V12Field))
    hfam hclosed
  · intro K hK
    exact hEq.equicontinuousOn K
  · intro K hK x hx
    refine ⟨Metric.closedBall (0 : V12Field) M,
      isCompact_closedBall 0 M, ?_⟩
    intro f hf
    simp only [Metric.mem_closedBall, dist_zero_left]
    exact hBound f hf x

#print axioms v12_ascoli_compact_closure

end SMScattering.W20Full
