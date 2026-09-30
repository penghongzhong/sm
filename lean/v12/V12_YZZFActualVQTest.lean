import lean.v12.V12_YZZBActualPotentialWeak
import lean.v12.V12_YZZEComponentTestLimits

/-! The actual reconstructed VQ distributional term, with its uniform
coefficient bound and weak limit proved from the original Q fields. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_VQ_compact_test_limit
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hmn : ∀ n, StronglyMeasurable (qn n)) (hmq : StronglyMeasurable q)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b)) (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hZq : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z)
    (j : Fin 2) (ψ : V12Spacetime → ℂ) (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    Tendsto (fun n => ∫ z,
      v12_actualPotentialL2Class hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n) z * (ψ z * qn n z j)
      ∂v12_slab_measure a b) atTop
        (𝓝 (∫ z, v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq z * (ψ z * q z j)
          ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  let Vn := fun n => v12_actualPotentialL2Class hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n)
  let V := v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq
  obtain ⟨C, hC, hB⟩ := v12_actualPotential_L2_budget hHLS
  have hbound : ∀ n, ‖Vn n‖ ≤ (24+C*M^2)*Z.toReal^2 := fun n =>
    hB a b (qn n) (hmn n) (hn4 n) M hM (hEn n) Z hZ (hZq n)
  have hw := v12_L2_dual_weak_to_integral μ Vn V
    (v12_actualPotential_weak_L2_limit hHLS a b qn q hmn hmq hn4 hq4 hn2 hq2 hlim
      M hM hEn hEq Z hZ hZq)
  have hnC (R n : ℕ) : MemLp (fun z => qn n z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 (qn n) (hn2 R n).aestronglyMeasurable j).trans_lt (hn2 R n)
  have hqC (R : ℕ) : MemLp (fun z => q z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 q (hq2 R).aestronglyMeasurable j).trans_lt (hq2 R)
  exact v12_weak_L2_local_strong_L2_compact_integral_limit a b Vn V ((24+C*M^2)*Z.toReal^2)
    hbound hw (fun n z => qn n z j) (fun z => q z j) hnC hqC
    (fun R => v12_raw_component_L2_limit _ qn q (hn2 R) (hq2 R) (hlim R) j) ψ hc hψ

#print axioms v12_actual_VQ_compact_test_limit
end SMScattering.W20Full
