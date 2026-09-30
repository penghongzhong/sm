import lean.v12.V12_YQWeakClosureFromLocal
import lean.v12.V12_YRActualCurvatureBounds

/-! Actual conjugate-quadratic tensors: global L2 bounds and weak convergence
are derived from the same Q fields and their local strong L2 convergence. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_tensorDensity (j k : Fin 2) (q : V12Field) : ℂ := star (q k) * q j

theorem v12_tensorDensity_continuous (j k : Fin 2) : Continuous (v12_tensorDensity j k) := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) k).continuous.star.mul
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous

theorem v12_tensorDensity_bound (j k : Fin 2) (q : V12Field) :
    ‖v12_tensorDensity j k q‖ ≤ ‖q‖ ^ 2 := by
  simp only [v12_tensorDensity, norm_mul, norm_star, pow_two]
  exact mul_le_mul (PiLp.norm_apply_le q k) (PiLp.norm_apply_le q j)
    (norm_nonneg _) (norm_nonneg _)

theorem v12_tensorDensity_L2_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (q : Ω → V12Field) (hq : AEStronglyMeasurable q μ) :
    eLpNorm (fun z => v12_tensorDensity j k (q z)) 2 μ ≤ (eLpNorm q 4 μ)^2 := by
  have hm := eLpNorm_mono_ae_real (p := (2 : ℝ≥0∞))
    ((v12_tensorDensity_continuous j k).comp_aestronglyMeasurable hq)
    (Filter.Eventually.of_forall (fun z => v12_tensorDensity_bound j k (q z)))
  have he : eLpNorm (fun z => ‖q z‖ ^ 2) 2 μ = (eLpNorm q 4 μ)^2 := by
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_two,
      show (2 : ℝ≥0∞) * 2 = 4 by norm_num] using
      (eLpNorm_norm_rpow (p := (2 : ℝ≥0∞)) (q := (2 : ℝ)) q hq (by norm_num))
  exact hm.trans_eq he

theorem v12_tensorDensity_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (q : Ω → V12Field) (hq : MemLp q 4 μ) :
    MemLp (fun z => v12_tensorDensity j k (q z)) 2 μ := by
  apply (v12_tensorDensity_L2_bound μ j k q hq.aestronglyMeasurable).trans_lt
  finiteness [hq.eLpNorm_ne_top]

noncomputable def v12_tensorL2Class
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (q : Ω → V12Field) (hq : MemLp q 4 μ) : Lp ℂ 2 μ :=
  (v12_tensorDensity_memLp μ j k q hq).toLp (fun z => v12_tensorDensity j k (q z))

theorem v12_tensorL2Class_budget
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (j k : Fin 2)
    (q : Ω → V12Field) (hq : MemLp q 4 μ) (Z : ℝ≥0∞) (hZ : Z ≠ ∞)
    (hb : eLpNorm q 4 μ ≤ Z) : ‖v12_tensorL2Class μ j k q hq‖ ≤ Z.toReal ^ 2 := by
  have he := (v12_tensorDensity_L2_bound μ j k q hq.aestronglyMeasurable).trans
    (pow_le_pow_left' hb 2)
  have h := ENNReal.toReal_mono (by finiteness) he
  simpa only [v12_tensorL2Class, Lp.norm_toLp, ENNReal.toReal_pow] using h

theorem v12_raw_L2_toLp_tendsto
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (fn : ℕ → Ω → E) (f : Ω → E)
    (hn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hlim : Tendsto (fun n => (eLpNorm (fun z => fn n z - f z) 2 μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (hn n).toLp (fn n)) atTop (𝓝 (hf.toLp f)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (n : ℕ) : dist ((hn n).toLp (fn n)) (hf.toLp f) =
      (eLpNorm (fun z => fn n z - f z) 2 μ).toReal := by
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    exact (hn n).coeFn_toLp.sub hf.coeFn_toLp
  simpa only [he] using hlim

theorem v12_actual_tensor_weak_L2_limit
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z)
    (j k : Fin 2) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b),
      Tendsto (fun n => ∫ z, v12_tensorDensity j k (qn n z) * φ z ∂v12_slab_measure a b) atTop
        (𝓝 (∫ z, v12_tensorDensity j k (q z) * φ z ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  let Qn := fun R n => (hn2 R n).toLp (qn n)
  let Q := fun R => (hq2 R).toLp q
  let Vn := fun n => v12_tensorL2Class μ j k (qn n) (hn4 n)
  let V := v12_tensorL2Class μ j k q hq4
  let Fn := fun R n => v12_tensorL1Class (μ.restrict (v12_spatial_cylinder R)) j k (Qn R n)
  let F := fun R => v12_tensorL1Class (μ.restrict (v12_spatial_cylinder R)) j k (Q R)
  have hrep (R : ℕ) (r : V12Spacetime → V12Field)
      (hr2 : MemLp r 2 (μ.restrict (v12_spatial_cylinder R))) (hr4 : MemLp r 4 μ) :
      (v12_tensorL1Class (μ.restrict (v12_spatial_cylinder R)) j k (hr2.toLp r) :
        V12Spacetime → ℂ) =ᵐ[μ.restrict (v12_spatial_cylinder R)]
        (v12_tensorL2Class μ j k r hr4 : V12Spacetime → ℂ) := by
    have hl := v12_tensorL1Class_ae _ j k (hr2.toLp r)
    have hg := ((v12_tensorDensity_memLp μ j k r hr4).coeFn_toLp).restrict
      (s := v12_spatial_cylinder R)
    filter_upwards [hl, hr2.coeFn_toLp, hg] with z hz hq hz2
    change v12_tensorL2Class μ j k r hr4 z = v12_tensorDensity j k (r z) at hz2
    rw [hz, hq, hz2]
    rfl
  have hF : ∀ R, Tendsto (Fn R) atTop (𝓝 (F R)) := by
    intro R
    exact (v12_tensorL1Class_continuous _ j k).tendsto _ |>.comp
      (v12_raw_L2_toLp_tendsto _ qn q (hn2 R) (hq2 R) (hlim R))
  have hw := v12_global_weak_L2_of_local_L1 a b Vn V (Z.toReal ^ 2)
    (fun n => v12_tensorL2Class_budget μ j k (qn n) (hn4 n) Z hZ (hb n)) Fn F
    (fun R n => hrep R (qn n) (hn2 R n) (hn4 n)) (fun R => hrep R q (hq2 R) hq4) hF
  have he (r : V12Spacetime → V12Field) (hr : MemLp r 4 μ) (φ : Lp ℂ 2 μ) :
      (∫ z, v12_tensorL2Class μ j k r hr z * φ z ∂μ) =
        ∫ z, v12_tensorDensity j k (r z) * φ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [(v12_tensorDensity_memLp μ j k r hr).coeFn_toLp] with z hz
    change v12_tensorL2Class μ j k r hr z = v12_tensorDensity j k (r z) at hz
    rw [hz]
  intro φ
  have hwφ := hw φ
  change Tendsto (fun n => ∫ z, v12_tensorL2Class μ j k (qn n) (hn4 n) z * φ z ∂μ) atTop
    (𝓝 (∫ z, v12_tensorL2Class μ j k q hq4 z * φ z ∂μ)) at hwφ
  simpa only [he] using hwφ

#print axioms v12_tensorDensity_L2_bound
#print axioms v12_raw_L2_toLp_tendsto
#print axioms v12_actual_tensor_weak_L2_limit
end SMScattering.W20Full
