import Mathlib
import «v12.V12_FrequencyTailAdapter»
import «v12.V12_LocalLimitCompatibility»

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

#print axioms v12_tightness_pipeline

end SMScattering.W20Full
