import Mathlib
import «v12.V12_FrequencyTightnessLimit»

namespace SMScattering.W20Full

open Filter
open scoped Topology

noncomputable def v12_tailSup
    (a b : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (k : ℕ) : ℝ :=
  sSup (Set.range (fun n => ‖Q n - P k (Q n)‖))

theorem v12_tail_range_bddAbove
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hM : 0 ≤ M)
    (hQ : ∀ n, ‖Q n‖ ≤ M)
    (hP : ∀ k, ‖P k‖ ≤ 1) :
    ∀ k, BddAbove (Set.range (fun n => ‖Q n - P k (Q n)‖)) := by
  intro k
  refine ⟨2 * M, ?_⟩
  rintro y ⟨n, rfl⟩
  have hPn0 : 0 ≤ ‖Q n‖ := norm_nonneg _
  have hPk0 : 0 ≤ ‖P k‖ := norm_nonneg _
  have hmap : ‖P k (Q n)‖ ≤ ‖P k‖ * ‖Q n‖ :=
    ContinuousLinearMap.le_opNorm (P k) (Q n)
  have hmapM : ‖P k (Q n)‖ ≤ M := by
    calc
      ‖P k (Q n)‖ ≤ ‖P k‖ * ‖Q n‖ := hmap
      _ ≤ 1 * M := by
        exact mul_le_mul (hP k) (hQ n) hPn0 (by norm_num)
      _ = M := one_mul M
  calc
    ‖Q n - P k (Q n)‖ ≤ ‖Q n‖ + ‖P k (Q n)‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hQ n) hmapM
    _ = 2 * M := by ring

theorem v12_tail_le_tailSup
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hM : 0 ≤ M)
    (hQ : ∀ n, ‖Q n‖ ≤ M)
    (hP : ∀ k, ‖P k‖ ≤ 1) :
    ∀ k n, ‖Q n - P k (Q n)‖ ≤ v12_tailSup a b Q P k := by
  intro k n
  unfold v12_tailSup
  exact le_csSup
    (v12_tail_range_bddAbove a b M Q P hM hQ hP k)
    (Set.mem_range_self n)

theorem v12_manuscript_tail_adapter
    (a b M : ℝ)
    (Q : ℕ → V12SlabL2 a b)
    (P : ℕ → V12SlabL2 a b →L[ℂ] V12SlabL2 a b)
    (hM : 0 ≤ M)
    (hQ : ∀ n, ‖Q n‖ ≤ M)
    (hP : ∀ k, ‖P k‖ ≤ 1)
    (hFreqTight :
      Tendsto (fun k => v12_tailSup a b Q P k) atTop (𝓝 0)) :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0)
        ∧
      ∀ k n, ‖Q n - P k (Q n)‖ ≤ err k := by
  refine ⟨fun k => v12_tailSup a b Q P k, hFreqTight, ?_⟩
  exact v12_tail_le_tailSup a b M Q P hM hQ hP

#print axioms v12_tail_range_bddAbove
#print axioms v12_tail_le_tailSup
#print axioms v12_manuscript_tail_adapter

end SMScattering.W20Full
