import lean.v12.V12_YSGActualWWeakClosure
import lean.v12.V12_YZZDCompactTestMultiplication

/-! Concrete component and conjugate-component tests for the original Q
sequence, including the actual W conjugate(Q) distributional source term. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_raw_component_eLpNorm_le
    (μ : Measure V12Spacetime) (p : ℝ≥0∞) (q : V12Spacetime → V12Field)
    (hq : AEStronglyMeasurable q μ) (j : Fin 2) :
    eLpNorm (fun z => q z j) p μ ≤ eLpNorm q p μ := by
  apply eLpNorm_mono_ae
    ((EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hq)
  exact Filter.Eventually.of_forall (fun z => PiLp.norm_apply_le (q z) j)

theorem v12_raw_component_L2_limit
    (μ : Measure V12Spacetime) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn : ∀ n, MemLp (qn n) 2 μ) (hq : MemLp q 2 μ)
    (hlim : Tendsto (fun n => (eLpNorm (fun z => qn n z-q z) 2 μ).toReal) atTop (𝓝 0))
    (j : Fin 2) :
    Tendsto (fun n => (eLpNorm (fun z => qn n z j-q z j) 2 μ).toReal) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ hlim
  intro n
  apply ENNReal.toReal_mono ((hn n).sub hq).eLpNorm_ne_top
  simpa only [PiLp.sub_apply, Pi.sub_apply] using v12_raw_component_eLpNorm_le μ 2
    (fun z => qn n z-q z) ((hn n).sub hq).aestronglyMeasurable j

theorem v12_actual_WQ_compact_test_limit
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z)
    (j : Fin 2) (ψ : V12Spacetime → ℂ) (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    Tendsto (fun n => ∫ z, v12_WDensity (qn n z) * (ψ z * star (qn n z j)) ∂v12_slab_measure a b)
      atTop (𝓝 (∫ z, v12_WDensity (q z) * (ψ z * star (q z j)) ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  have hnC (R n : ℕ) : MemLp (fun z => qn n z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 (qn n) (hn2 R n).aestronglyMeasurable j).trans_lt (hn2 R n)
  have hqC (R : ℕ) : MemLp (fun z => q z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 q (hq2 R).aestronglyMeasurable j).trans_lt (hq2 R)
  have hnS (R n : ℕ) : MemLp (fun z => star (qn n z j)) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (hnC R n).star
  have hqS (R : ℕ) : MemLp (fun z => star (q z j)) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (hqC R).star
  have hS (R : ℕ) : Tendsto (fun n => (eLpNorm (fun z => star (qn n z j)-star (q z j)) 2
      (μ.restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    have he (n : ℕ) : (fun z => star (qn n z j)-star (q z j)) =
        star (fun z => qn n z j-q z j) := by funext z; simp only [Pi.star_apply, star_sub]
    simp only [he, eLpNorm_star]
    exact v12_raw_component_L2_limit _ qn q (hn2 R) (hq2 R) (hlim R) j
  have he (r : V12Spacetime → V12Field) (hr : MemLp r 4 μ) (g : V12Spacetime → ℂ) :
      (∫ z, v12_WL2Class μ r hr z * g z ∂μ) = ∫ z, v12_WDensity (r z) * g z ∂μ := by
    apply integral_congr_ae
    filter_upwards [(v12_actual_W_mass_L2_budgets μ r hr).1.coeFn_toLp] with z hz
    change v12_WL2Class μ r hr z = v12_WDensity (r z) at hz
    rw [hz]
  have hw : ∀ φ : Lp ℂ 2 μ,
      Tendsto (fun n => ∫ z, v12_WL2Class μ (qn n) (hn4 n) z * φ z ∂μ) atTop
        (𝓝 (∫ z, v12_WL2Class μ q hq4 z * φ z ∂μ)) := by
    intro φ
    simpa only [he] using v12_actual_W_weak_L2_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hb φ
  have h := v12_weak_L2_local_strong_L2_compact_integral_limit a b
    (fun n => v12_WL2Class μ (qn n) (hn4 n)) (v12_WL2Class μ q hq4) (2*Z.toReal^2)
    (fun n => v12_WL2Class_budget μ (qn n) (hn4 n) Z hZ (hb n)) hw
    (fun n z => star (qn n z j)) (fun z => star (q z j)) hnS hqS hS ψ hc hψ
  change Tendsto (fun n => ∫ z, v12_WL2Class μ (qn n) (hn4 n) z * (ψ z*star (qn n z j)) ∂μ)
    atTop (𝓝 (∫ z, v12_WL2Class μ q hq4 z * (ψ z*star (q z j)) ∂μ)) at h
  simpa only [he] using h

#print axioms v12_raw_component_L2_limit
#print axioms v12_actual_WQ_compact_test_limit
end SMScattering.W20Full
