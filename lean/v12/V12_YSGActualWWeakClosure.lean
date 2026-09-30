import lean.v12.V12_YRTensorWeakClosure
import lean.v12.V12_YRZZeroOrderAlgebra

/-! Weak L2 closure for the original W=2(Q_0^2+Q_1^2), derived from
local strong Q convergence and the actual global Q L4 bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_WL2Class {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → V12Field) (hq : MemLp q 4 μ) : Lp ℂ 2 μ :=
  (v12_actual_W_mass_L2_budgets μ q hq).1.toLp (fun z => v12_WDensity (q z))

theorem v12_WL2Class_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → V12Field) (hq : MemLp q 4 μ)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : eLpNorm q 4 μ ≤ Z) :
    ‖v12_WL2Class μ q hq‖ ≤ 2*Z.toReal^2 := by
  have he := (v12_actual_W_mass_L2_budgets μ q hq).2.2.1.trans
    (mul_le_mul' le_rfl (pow_le_pow_left' hb 2))
  have h := ENNReal.toReal_mono (by finiteness) he
  simpa only [v12_WL2Class, Lp.norm_toLp, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow] using h

theorem v12_actual_W_weak_L2_limit
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b),
      Tendsto (fun n => ∫ z, v12_WDensity (qn n z) * φ z ∂v12_slab_measure a b) atTop
        (𝓝 (∫ z, v12_WDensity (q z) * φ z ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  let Fn := fun R n => v12_W_L1Class (μ.restrict (v12_spatial_cylinder R)) ((hn2 R n).toLp (qn n))
  let F := fun R => v12_W_L1Class (μ.restrict (v12_spatial_cylinder R)) ((hq2 R).toLp q)
  have hr (R : ℕ) (r : V12Spacetime → V12Field)
      (hr2 : MemLp r 2 (μ.restrict (v12_spatial_cylinder R))) (hr4 : MemLp r 4 μ) :
      (v12_W_L1Class (μ.restrict (v12_spatial_cylinder R)) (hr2.toLp r) : V12Spacetime → ℂ)
        =ᵐ[μ.restrict (v12_spatial_cylinder R)] (v12_WL2Class μ r hr4 : V12Spacetime → ℂ) := by
    filter_upwards [v12_W_L1Class_ae _ (hr2.toLp r), hr2.coeFn_toLp,
      ((v12_actual_W_mass_L2_budgets μ r hr4).1.coeFn_toLp).restrict
        (s := v12_spatial_cylinder R)] with z hl hq hg
    change v12_WL2Class μ r hr4 z = v12_WDensity (r z) at hg
    rw [hl, hq, hg]
    rfl
  have hF : ∀ R, Tendsto (Fn R) atTop (𝓝 (F R)) := by
    intro R
    exact v12_W_strong_L1 _ _ _
      (v12_raw_L2_toLp_tendsto _ qn q (hn2 R) (hq2 R) (hlim R))
  have hw := v12_global_weak_L2_of_local_L1 a b
    (fun n => v12_WL2Class μ (qn n) (hn4 n)) (v12_WL2Class μ q hq4) (2*Z.toReal^2)
    (fun n => v12_WL2Class_budget μ (qn n) (hn4 n) Z hZ (hb n)) Fn F
    (fun R n => hr R (qn n) (hn2 R n) (hn4 n)) (fun R => hr R q (hq2 R) hq4) hF
  have he (r : V12Spacetime → V12Field) (hr4 : MemLp r 4 μ) (φ : Lp ℂ 2 μ) :
      (∫ z, v12_WL2Class μ r hr4 z * φ z ∂μ) = ∫ z, v12_WDensity (r z) * φ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [(v12_actual_W_mass_L2_budgets μ r hr4).1.coeFn_toLp] with z hz
    change v12_WL2Class μ r hr4 z = v12_WDensity (r z) at hz
    rw [hz]
  intro φ
  have h := hw φ
  change Tendsto (fun n => ∫ z, v12_WL2Class μ (qn n) (hn4 n) z * φ z ∂μ) atTop
    (𝓝 (∫ z, v12_WL2Class μ q hq4 z * φ z ∂μ)) at h
  simpa only [he] using h

#print axioms v12_W_L1Class_ae
#print axioms v12_WL2Class_budget
#print axioms v12_actual_W_weak_L2_limit
end SMScattering.W20Full
