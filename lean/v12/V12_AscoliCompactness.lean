import Mathlib
import «v12.V12_FrequencyTightnessLimit»

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


theorem v12_ascoli_L2_compact_closure
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : ℕ → C(X, V12Field))
    (M : ℝ) (hM : 0 ≤ M)
    (hEq :
      Equicontinuous
        ((↑) : Set.range F → X → V12Field))
    (hBound : ∀ n x, ‖F n x‖ ≤ M) :
    IsCompact
      (closure
        (Set.range
          (fun n =>
            ContinuousMap.toLp 2 μ ℂ (F n)))) := by
  let S : Set C(X, V12Field) := Set.range F
  have hScompact : IsCompact (closure S) := by
    apply v12_ascoli_compact_closure S M hM hEq
    intro f hf x
    obtain ⟨n, rfl⟩ := hf
    exact hBound n x
  let T : C(X, V12Field) →L[ℂ] Lp V12Field 2 μ :=
    ContinuousMap.toLp 2 μ ℂ
  have hImageCompact : IsCompact (T '' closure S) :=
    hScompact.image T.continuous
  have hImageClosed : IsClosed (T '' closure S) :=
    hImageCompact.isClosed
  have hRangeSubset : Set.range (fun n => T (F n)) ⊆ T '' closure S := by
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨F n, subset_closure (Set.mem_range_self n), rfl⟩
  have hClosureSubset :
      closure (Set.range (fun n => T (F n))) ⊆ T '' closure S :=
    closure_minimal hRangeSubset hImageClosed
  exact hImageCompact.of_isClosed_subset isClosed_closure hClosureSubset

#print axioms v12_ascoli_L2_compact_closure

#print axioms v12_ascoli_compact_closure

end SMScattering.W20Full
