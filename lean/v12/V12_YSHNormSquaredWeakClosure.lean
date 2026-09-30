import lean.v12.V12_YRTensorWeakClosure

/-! Norm-square weak closure for real Hilbert-valued fields. This will be
applied to the actual spatial Hodge field in V=-A0+|A|^2-2m. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def v12_normSqL1Class {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp E 2 μ) : Lp ℂ 1 μ :=
  Complex.ofRealCLM.compLp ((innerSL ℝ (E := E)).holder 1 f f)

theorem v12_normSqL1Class_continuous {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) : Continuous (v12_normSqL1Class (E := E) μ) := by
  have h := ((innerSL ℝ (E := E)).holderL μ 2 2 1).continuous₂.comp
    (continuous_id.prodMk continuous_id)
  have hh := (Complex.ofRealCLM.compLpL 1 μ).continuous.comp h
  have hc (r : Lp ℝ 1 μ) : Complex.ofRealCLM.compLpL 1 μ r = Complex.ofRealCLM.compLp r := rfl
  unfold v12_normSqL1Class
  simpa only [Function.comp_def, Function.uncurry, ContinuousLinearMap.holderL_apply_apply,
    id_eq, hc] using hh

theorem v12_normSqL1Class_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp E 2 μ) :
    (v12_normSqL1Class μ f : Ω → ℂ) =ᵐ[μ] fun z => (‖f z‖^2 : ℝ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLp ((innerSL ℝ (E := E)).holder 1 f f),
    (innerSL ℝ (E := E)).coeFn_holder (r := 1) f f] with z hc hi
  change v12_normSqL1Class μ f z = (((innerSL ℝ (E := E)).holder 1 f f) z : ℂ) at hc
  rw [hc, hi]
  simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq]

theorem v12_normSq_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → E) (hf : MemLp f 4 μ) :
    MemLp (fun z => ((‖f z‖^2 : ℝ) : ℂ)) 2 μ := by
  have he : eLpNorm (fun z => ((‖f z‖^2 : ℝ) : ℂ)) 2 μ = (eLpNorm f 4 μ)^2 := by
    have hP : Continuous (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by fun_prop
    have hm : AEStronglyMeasurable (fun z => ((‖f z‖^2 : ℝ) : ℂ)) μ :=
      hP.comp_aestronglyMeasurable hf.aestronglyMeasurable
    rw [← eLpNorm_norm (fun z => ((‖f z‖^2 : ℝ) : ℂ)) hm]
    simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_two,
      show (2 : ℝ≥0∞)*2=4 by norm_num] using
      eLpNorm_norm_rpow (p := (2 : ℝ≥0∞)) (q := (2 : ℝ)) f hf.aestronglyMeasurable (by norm_num)
  change eLpNorm _ 2 μ < ∞
  rw [he]
  finiteness [hf.eLpNorm_ne_top]

noncomputable def v12_normSqL2Class {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → E) (hf : MemLp f 4 μ) : Lp ℂ 2 μ :=
  (v12_normSq_memLp_two μ f hf).toLp (fun z => (‖f z‖^2 : ℝ))

theorem v12_normSqL2Class_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → E) (hf : MemLp f 4 μ)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : eLpNorm f 4 μ ≤ Z) :
    ‖v12_normSqL2Class μ f hf‖ ≤ Z.toReal^2 := by
  have he : eLpNorm (fun z => ((‖f z‖^2 : ℝ) : ℂ)) 2 μ = (eLpNorm f 4 μ)^2 := by
    have hP : Continuous (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by fun_prop
    have hm : AEStronglyMeasurable (fun z => ((‖f z‖^2 : ℝ) : ℂ)) μ :=
      hP.comp_aestronglyMeasurable hf.aestronglyMeasurable
    rw [← eLpNorm_norm (fun z => ((‖f z‖^2 : ℝ) : ℂ)) hm]
    simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_two,
      show (2 : ℝ≥0∞)*2=4 by norm_num] using
      eLpNorm_norm_rpow (p := (2 : ℝ≥0∞)) (q := (2 : ℝ)) f hf.aestronglyMeasurable (by norm_num)
  have h := ENNReal.toReal_mono (by finiteness : Z^2 ≠ ∞) (he.le.trans (pow_le_pow_left' hb 2))
  simpa only [v12_normSqL2Class, Lp.norm_toLp, ENNReal.toReal_pow] using h

theorem v12_normSq_weak_L2_limit
    (a b : ℝ) (fn : ℕ → V12Spacetime → E) (f : V12Spacetime → E)
    (hn4 : ∀ n, MemLp (fn n) 4 (v12_slab_measure a b))
    (hf4 : MemLp f 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (fn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hf2 : ∀ R, MemLp f 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => fn n z-f z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (fn n) 4 (v12_slab_measure a b) ≤ Z) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b),
      Tendsto (fun n => ∫ z, v12_normSqL2Class (v12_slab_measure a b) (fn n) (hn4 n) z * φ z
        ∂v12_slab_measure a b) atTop
        (𝓝 (∫ z, v12_normSqL2Class (v12_slab_measure a b) f hf4 z * φ z ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  let Fn := fun R n => v12_normSqL1Class (μ.restrict (v12_spatial_cylinder R)) ((hn2 R n).toLp (fn n))
  let F := fun R => v12_normSqL1Class (μ.restrict (v12_spatial_cylinder R)) ((hf2 R).toLp f)
  have hr (R : ℕ) (r : V12Spacetime → E)
      (hr2 : MemLp r 2 (μ.restrict (v12_spatial_cylinder R))) (hr4 : MemLp r 4 μ) :
      (v12_normSqL1Class (μ.restrict (v12_spatial_cylinder R)) (hr2.toLp r) : V12Spacetime → ℂ)
        =ᵐ[μ.restrict (v12_spatial_cylinder R)] (v12_normSqL2Class μ r hr4 : V12Spacetime → ℂ) := by
    filter_upwards [v12_normSqL1Class_ae _ (hr2.toLp r), hr2.coeFn_toLp,
      ((v12_normSq_memLp_two μ r hr4).coeFn_toLp).restrict
        (s := v12_spatial_cylinder R)] with z hl hq hg
    change v12_normSqL2Class μ r hr4 z = ((‖r z‖^2 : ℝ) : ℂ) at hg
    rw [hl, hq, hg]
  have hF : ∀ R, Tendsto (Fn R) atTop (𝓝 (F R)) := by
    intro R
    exact (v12_normSqL1Class_continuous _).tendsto _ |>.comp
      (v12_raw_L2_toLp_tendsto _ fn f (hn2 R) (hf2 R) (hlim R))
  exact v12_global_weak_L2_of_local_L1 a b
    (fun n => v12_normSqL2Class μ (fn n) (hn4 n)) (v12_normSqL2Class μ f hf4) (Z.toReal^2)
    (fun n => v12_normSqL2Class_budget μ (fn n) (hn4 n) Z hZ (hb n)) Fn F
    (fun R n => hr R (fn n) (hn2 R n) (hn4 n)) (fun R => hr R f (hf2 R) hf4) hF

#print axioms v12_normSqL1Class_continuous
#print axioms v12_normSqL1Class_ae
#print axioms v12_normSqL2Class_budget
#print axioms v12_normSq_weak_L2_limit
end SMScattering.W20Full
