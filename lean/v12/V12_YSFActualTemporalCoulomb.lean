import lean.v12.V12_YQWeakDualConversion
import lean.v12.V12_YRTensorWeakClosure
import lean.v12.V12_YSDSpacetimeRiesz

/-! Reconstruct S, mass and A0 from the same raw Q fields. The weak limit
of A0 is proved from local strong Q convergence and the uniform Q L4 budget;
neither weak convergence of coefficients nor an abstract Riesz realization
is an input. Real-valuedness of the Fourier output is a separate obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_SL2Class {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (j k : Fin 2) (q : Ω → V12Field) (hq : MemLp q 4 μ) : Lp ℂ 2 μ :=
  (1 / 2 : ℂ) • (v12_tensorL2Class μ j k q hq + v12_tensorL2Class μ k j q hq)

noncomputable def v12_massComplexL2Class {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → V12Field) (hq : MemLp q 4 μ) : Lp ℂ 2 μ :=
  v12_tensorL2Class μ 0 0 q hq + v12_tensorL2Class μ 1 1 q hq

theorem v12_SL2Class_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (j k : Fin 2) (q : Ω → V12Field) (hq : MemLp q 4 μ) :
    (v12_SL2Class μ j k q hq : Ω → ℂ) =ᵐ[μ]
      fun z => ((v12_tensorDensity j k (q z)).re : ℂ) := by
  let T := fun i l => v12_tensorL2Class μ i l q hq
  filter_upwards [Lp.coeFn_smul (1/2 : ℂ) (T j k + T k j), Lp.coeFn_add (T j k) (T k j),
    (v12_tensorDensity_memLp μ j k q hq).coeFn_toLp,
    (v12_tensorDensity_memLp μ k j q hq).coeFn_toLp] with z hsm hadd hj hk
  change v12_SL2Class μ j k q hq z = (1/2 : ℂ) • (T j k + T k j) z at hsm
  change T j k z = v12_tensorDensity j k (q z) at hj
  change T k j z = v12_tensorDensity k j (q z) at hk
  rw [hsm, hadd, Pi.add_apply, hj, hk, smul_eq_mul]
  apply Complex.ext <;> simp [v12_tensorDensity, Complex.mul_re, Complex.mul_im] <;> ring

theorem v12_massComplexL2Class_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → V12Field) (hq : MemLp q 4 μ) :
    (v12_massComplexL2Class μ q hq : Ω → ℂ) =ᵐ[μ] fun z => (‖q z‖^2 : ℝ) := by
  filter_upwards [Lp.coeFn_add (v12_tensorL2Class μ 0 0 q hq) (v12_tensorL2Class μ 1 1 q hq),
    (v12_tensorDensity_memLp μ 0 0 q hq).coeFn_toLp,
    (v12_tensorDensity_memLp μ 1 1 q hq).coeFn_toLp] with z hadd h0 h1
  change v12_massComplexL2Class μ q hq z =
    v12_tensorL2Class μ 0 0 q hq z + v12_tensorL2Class μ 1 1 q hq z at hadd
  change v12_tensorL2Class μ 0 0 q hq z = v12_tensorDensity 0 0 (q z) at h0
  change v12_tensorL2Class μ 1 1 q hq z = v12_tensorDensity 1 1 (q z) at h1
  rw [hadd, h0, h1]
  have he : ‖q z‖^2 = ‖q z 0‖^2 + ‖q z 1‖^2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  rw [he]
  simp only [v12_tensorDensity, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Complex.ofReal_add]

noncomputable def v12_actualTemporalCoulombL2 (a b : ℝ)
    (q : V12Spacetime → V12Field) (hq : MemLp q 4 (v12_slab_measure a b)) :
    Lp ℂ 2 (v12_slab_measure a b) :=
  (4 : ℂ) • (∑ j, ∑ k, v12_spacetimeCoulombRieszOperator
    ((volume : Measure ℝ).restrict (Set.Icc a b)) j k
      (v12_SL2Class (v12_slab_measure a b) j k q hq)) -
    (2 : ℂ) • v12_massComplexL2Class (v12_slab_measure a b) q hq

theorem v12_actualTemporalCoulomb_L2_budget
    (a b : ℝ) (q : V12Spacetime → V12Field) (hq : MemLp q 4 (v12_slab_measure a b))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : eLpNorm q 4 (v12_slab_measure a b) ≤ Z) :
    ‖v12_actualTemporalCoulombL2 a b q hq‖ ≤ 20 * Z.toReal^2 := by
  let μ := v12_slab_measure a b
  have hT (j k : Fin 2) := v12_tensorL2Class_budget μ j k q hq Z hZ hb
  have hS (j k : Fin 2) : ‖v12_SL2Class μ j k q hq‖ ≤ Z.toReal^2 := by
    unfold v12_SL2Class
    rw [norm_smul]
    have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hc]
    have hsum := (norm_add_le (v12_tensorL2Class μ j k q hq)
      (v12_tensorL2Class μ k j q hq)).trans (add_le_add (hT j k) (hT k j))
    nlinarith
  have hm : ‖v12_massComplexL2Class μ q hq‖ ≤ 2*Z.toReal^2 := by
    exact (norm_add_le _ _).trans (by simpa only [two_mul] using add_le_add (hT 0 0) (hT 1 1))
  have hs : ‖∑ j, ∑ k, v12_spacetimeCoulombRieszOperator
      ((volume : Measure ℝ).restrict (Set.Icc a b)) j k (v12_SL2Class μ j k q hq)‖ ≤ 4*Z.toReal^2 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : Fin 2, ∑ _k : Fin 2, Z.toReal^2 := by
        apply Finset.sum_le_sum
        intro j hj
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        exact (v12_spacetimeCoulombRieszOperator_bound _ j k _).trans (hS j k)
      _ = _ := by simp; ring
  unfold v12_actualTemporalCoulombL2
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, Complex.norm_ofNat]
  nlinarith

theorem v12_actualTensorL2_dual_limit
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z) (j k : Fin 2) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b) →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_tensorL2Class (v12_slab_measure a b) j k (qn n) (hn4 n))) atTop
        (𝓝 (φ (v12_tensorL2Class (v12_slab_measure a b) j k q hq4))) := by
  let μ := v12_slab_measure a b
  have hw (j k : Fin 2) : ∀ φ : Lp ℂ 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_tensorL2Class μ j k (qn n) (hn4 n))) atTop
        (𝓝 (φ (v12_tensorL2Class μ j k q hq4))) := by
    apply v12_L2_integral_weak_to_dual
    intro ψ
    have he (r : V12Spacetime → V12Field) (hr : MemLp r 4 μ) :
        (∫ z, v12_tensorL2Class μ j k r hr z * ψ z ∂μ) =
          ∫ z, v12_tensorDensity j k (r z) * ψ z ∂μ := by
      apply integral_congr_ae
      filter_upwards [(v12_tensorDensity_memLp μ j k r hr).coeFn_toLp] with z hz
      change v12_tensorL2Class μ j k r hr z = v12_tensorDensity j k (r z) at hz
      rw [hz]
    simpa only [he] using v12_actual_tensor_weak_L2_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hb j k ψ
  exact hw j k

theorem v12_actualMassL2_dual_limit
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b) →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_massComplexL2Class (v12_slab_measure a b) (qn n) (hn4 n))) atTop
        (𝓝 (φ (v12_massComplexL2Class (v12_slab_measure a b) q hq4))) := by
  intro φ
  have h0 := v12_actualTensorL2_dual_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hb 0 0 φ
  have h1 := v12_actualTensorL2_dual_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hb 1 1 φ
  simpa only [v12_massComplexL2Class, map_add] using h0.add h1

theorem v12_actualTemporalCoulomb_weak_L2_limit
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b) →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_actualTemporalCoulombL2 a b (qn n) (hn4 n))) atTop
        (𝓝 (φ (v12_actualTemporalCoulombL2 a b q hq4))) := by
  let μ := v12_slab_measure a b
  have hw (j k : Fin 2) : ∀ φ : Lp ℂ 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_tensorL2Class μ j k (qn n) (hn4 n))) atTop
        (𝓝 (φ (v12_tensorL2Class μ j k q hq4))) := by
    apply v12_L2_integral_weak_to_dual
    intro ψ
    have he (r : V12Spacetime → V12Field) (hr : MemLp r 4 μ) :
        (∫ z, v12_tensorL2Class μ j k r hr z * ψ z ∂μ) =
          ∫ z, v12_tensorDensity j k (r z) * ψ z ∂μ := by
      apply integral_congr_ae
      filter_upwards [(v12_tensorDensity_memLp μ j k r hr).coeFn_toLp] with z hz
      change v12_tensorL2Class μ j k r hr z = v12_tensorDensity j k (r z) at hz
      rw [hz]
    simpa only [he] using v12_actual_tensor_weak_L2_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hb j k ψ
  have hS (j k : Fin 2) (φ : Lp ℂ 2 μ →L[ℂ] ℂ) :
      Tendsto (fun n => φ (v12_SL2Class μ j k (qn n) (hn4 n))) atTop
        (𝓝 (φ (v12_SL2Class μ j k q hq4))) := by
    simpa only [v12_SL2Class, map_smul, map_add] using ((hw j k φ).add (hw k j φ)).const_smul (1/2 : ℂ)
  have hm (φ : Lp ℂ 2 μ →L[ℂ] ℂ) :
      Tendsto (fun n => φ (v12_massComplexL2Class μ (qn n) (hn4 n))) atTop
        (𝓝 (φ (v12_massComplexL2Class μ q hq4))) := by
    simpa only [v12_massComplexL2Class, map_add] using (hw 0 0 φ).add (hw 1 1 φ)
  intro φ
  have hR (j k : Fin 2) := hS j k
    (φ.comp (v12_spacetimeCoulombRieszOperator ((volume : Measure ℝ).restrict (Set.Icc a b)) j k))
  have hs := tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_finset_sum Finset.univ (fun k _ => hR j k))
  simpa only [v12_actualTemporalCoulombL2, map_sub, map_smul, map_sum,
    ContinuousLinearMap.comp_apply] using (hs.const_smul (4 : ℂ)).sub ((hm φ).const_smul (2 : ℂ))

#print axioms v12_actualTemporalCoulomb_L2_budget
#print axioms v12_actualTensorL2_dual_limit
#print axioms v12_actualMassL2_dual_limit
#print axioms v12_SL2Class_ae
#print axioms v12_massComplexL2Class_ae
#print axioms v12_actualTemporalCoulomb_weak_L2_limit
end SMScattering.W20Full
