import Mathlib
import «v12.V12_FrequencyTailAdapter»
import «v12.V12_LocalLimitCompatibility»
import «v12.V12_AscoliCompactness»

namespace SMScattering.W20Full

open Filter
open scoped Topology

/--
One statement assembling the actual manuscript tail quantifier, the single
subsequence extraction, and compatibility of all local L2 limits.

The only remaining analytic input here is fixed-cutoff local compactness.
-/
theorem v12_tightness_pipeline
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hM : 0 ≤ M)
    (hQ : ∀ n, ‖Q n‖ ≤ M)
    (hP : ∀ k, ‖P k‖ ≤ 1)
    (hFreqTight :
      Tendsto (fun k => v12_tailSup a b Q P k) atTop (𝓝 0))
    (hCompact : ∀ R k, IsCompact
      (closure (Set.range (fun n => v12_localize a b R (P k (Q n)))))) :
    ∃ (σ : ℕ → ℕ) (q : ∀ R, V12CylinderL2 a b R),
      StrictMono σ
        ∧
      (∀ R,
        Tendsto (fun n => v12_localize a b R (Q (σ n)))
          atTop (𝓝 (q R)))
        ∧
      (∀ {R S : ℕ} (hRS : R ≤ S),
        v12_localize_nested a b hRS (q S) = q R) := by
  obtain ⟨err, hErr, hTail⟩ :=
    v12_manuscript_tail_adapter a b M Q P hM hQ hP hFreqTight
  obtain ⟨σ, hσ, hlim⟩ :=
    v12_spacetime_L2_common_subsequence a b Q P err hErr hTail hCompact
  choose q hq using hlim
  refine ⟨σ, q, hσ, hq, ?_⟩
  intro R S hRS
  exact v12_common_subsequence_local_compatibility a b Q σ q hq hRS


/--
Fixed-cutoff local compactness follows once every localized cutoff is realized
as the image, under one continuous linear local realization map, of a uniformly
bounded equicontinuous family on a compact parameter domain.

This is the exact bridge from the manuscript's fixed-frequency space/time
bounds to the hCompact input of v12_tightness_pipeline.
-/
theorem v12_fixed_cutoff_compact_from_ascoli
    (a b : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (X : ℕ → Type*)
    [∀ R, MetricSpace (X R)]
    [∀ R, CompactSpace (X R)]
    (F : ∀ R k, ℕ → C(X R, V12Field))
    (J : ∀ R, C(X R, V12Field) →L[ℂ] V12CylinderL2 a b R)
    (Mloc : ℕ → ℕ → ℝ)
    (hMloc : ∀ R k, 0 ≤ Mloc R k)
    (hEq : ∀ R k,
      Equicontinuous
        ((↑) : Set.range (F R k) → X R → V12Field))
    (hBound : ∀ R k n x, ‖F R k n x‖ ≤ Mloc R k)
    (hRep : ∀ R k n,
      J R (F R k n) = v12_localize a b R (P k (Q n))) :
    ∀ R k, IsCompact
      (closure (Set.range (fun n => v12_localize a b R (P k (Q n))))) := by
  intro R k
  have hc :=
    v12_ascoli_continuous_image_compact_closure
      (F R k) (J R) (Mloc R k) (hMloc R k) (hEq R k)
      (fun n x => hBound R k n x)
  have hfun :
      (fun n => J R (F R k n))
        =
      (fun n => v12_localize a b R (P k (Q n))) := by
    funext n
    exact hRep R k n
  simpa [hfun] using hc

/--
Full structural form of the tightness argument: fixed-cutoff representatives
satisfy Ascoli, the manuscript frequency-tail supremum tends to zero, and one
single subsequence then converges in every local L2 space with compatible
limits.
-/
theorem v12_tightness_from_ascoli_and_tail
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hM : 0 ≤ M)
    (hQ : ∀ n, ‖Q n‖ ≤ M)
    (hP : ∀ k, ‖P k‖ ≤ 1)
    (hFreqTight :
      Tendsto (fun k => v12_tailSup a b Q P k) atTop (𝓝 0))
    (X : ℕ → Type*)
    [∀ R, MetricSpace (X R)]
    [∀ R, CompactSpace (X R)]
    (F : ∀ R k, ℕ → C(X R, V12Field))
    (J : ∀ R, C(X R, V12Field) →L[ℂ] V12CylinderL2 a b R)
    (Mloc : ℕ → ℕ → ℝ)
    (hMloc : ∀ R k, 0 ≤ Mloc R k)
    (hEq : ∀ R k,
      Equicontinuous
        ((↑) : Set.range (F R k) → X R → V12Field))
    (hBound : ∀ R k n x, ‖F R k n x‖ ≤ Mloc R k)
    (hRep : ∀ R k n,
      J R (F R k n) = v12_localize a b R (P k (Q n))) :
    ∃ (σ : ℕ → ℕ) (q : ∀ R, V12CylinderL2 a b R),
      StrictMono σ
        ∧
      (∀ R,
        Tendsto (fun n => v12_localize a b R (Q (σ n)))
          atTop (𝓝 (q R)))
        ∧
      (∀ {R S : ℕ} (hRS : R ≤ S),
        v12_localize_nested a b hRS (q S) = q R) := by
  have hCompact :=
    v12_fixed_cutoff_compact_from_ascoli
      a b Q P X F J Mloc hMloc hEq hBound hRep
  exact v12_tightness_pipeline
    a b M Q P hM hQ hP hFreqTight hCompact

#print axioms v12_fixed_cutoff_compact_from_ascoli
#print axioms v12_tightness_from_ascoli_and_tail

#print axioms v12_tightness_pipeline

end SMScattering.W20Full
