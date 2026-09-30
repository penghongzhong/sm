import lean.v12.V12_YWCoulombDriftBudget
import lean.v12.V12_YZYHodgeStrongLocal

/-! The actual A_j Q product is strongly L1 continuous along the original
sequence. This uses the proved same-field Hodge local L2 limit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_raw_L2_drift_L1_limit
    (μ : Measure V12Spacetime) (An : ℕ → V12Spacetime → ℂ) (A : V12Spacetime → ℂ)
    (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hAn : ∀ n, MemLp (An n) 2 μ) (hA : MemLp A 2 μ)
    (hqn : ∀ n, MemLp (qn n) 2 μ) (hq : MemLp q 2 μ)
    (ha : Tendsto (fun n => (eLpNorm (fun z => An n z-A z) 2 μ).toReal) atTop (𝓝 0))
    (hql : Tendsto (fun n => (eLpNorm (fun z => qn n z-q z) 2 μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (fun z => An n z • qn n z - A z • q z) 1 μ).toReal)
      atTop (𝓝 0) := by
  let Fn := fun n => v12_driftL1Class μ ((hAn n).toLp (An n)) ((hqn n).toLp (qn n))
  let F := v12_driftL1Class μ (hA.toLp A) (hq.toLp q)
  have ht := v12_strong_L2_drift_product_limit μ
    (fun n => (hAn n).toLp (An n)) (fun n => (hqn n).toLp (qn n)) (hA.toLp A) (hq.toLp q)
    (v12_raw_L2_toLp_tendsto μ An A hAn hA ha)
    (v12_raw_L2_toLp_tendsto μ qn q hqn hq hql)
  have hr (a : V12Spacetime → ℂ) (r : V12Spacetime → V12Field)
      (ha : MemLp a 2 μ) (hr : MemLp r 2 μ) :
      (v12_driftL1Class μ (ha.toLp a) (hr.toLp r) : V12Spacetime → V12Field) =ᵐ[μ]
        fun z => a z • r z :=
    v12_driftL1Class_raw_rep μ _ _ a r ha.coeFn_toLp hr.coeFn_toLp
  have he (n : ℕ) : ‖Fn n-F‖ = (eLpNorm (fun z => An n z • qn n z-A z • q z) 1 μ).toReal := by
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans ((hr (An n) (qn n) (hAn n) (hqn n)).sub (hr A q hA hq))
  change Tendsto Fn atTop (𝓝 F) at ht
  have h := (ht.sub_const F).norm
  simpa only [sub_self, norm_zero, he] using h

theorem v12_actual_Coulomb_drift_local_L1_limit
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (R : ℕ) (j : Fin 2)
    (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hmn : ∀ n, StronglyMeasurable (qn n)) (hmq : StronglyMeasurable q)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b)) (hq4 : MemLp q 4 (v12_slab_measure a b))
    (hn2 : ∀ S n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder S)))
    (hq2 : ∀ S, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder S)))
    (hlim : ∀ S, Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder S))).toReal) atTop (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hZq : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z) :
    Tendsto (fun n => (eLpNorm (fun z => v12_actualCoulombA (qn n) j z • qn n z -
      v12_actualCoulombA q j z • q z) 1
        ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
  let μ := v12_slab_measure a b
  let ν := μ.restrict (v12_spatial_cylinder R)
  obtain ⟨hAd, hAlim⟩ := v12_actual_Hodge_local_L2_limit hHLS a b R qn q hmn hmq
    hn4 hq4 hn2 hq2 hlim M hM hEn hEq Z hZ hZq
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  have hA2 (r : V12Spacetime → V12Field) (hr : StronglyMeasurable r) (hr4 : MemLp r 4 μ)
      (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => r (t,x)) 2 volume ≤ ENNReal.ofReal M) :
      MemLp (v12_actualCoulombA r j) 2 ν := by
    have h4 := (hH a b r hr hr4 (ENNReal.ofReal M) (by finiteness) hE).1
    have hc4 : MemLp (v12_actualCoulombA r j) 4 μ :=
      (v12_actualCoulombA_eLpNorm_le μ r hr 4 j).trans_lt h4
    exact (hc4.restrict (v12_spatial_cylinder R)).mono_exponent (by norm_num)
  have hb (n : ℕ) :
      eLpNorm (fun z => v12_actualCoulombA (qn n) j z-v12_actualCoulombA q j z) 2 ν ≤
        eLpNorm (fun z => v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z) 2 ν := by
    apply eLpNorm_mono_ae
    · exact ((hA2 (qn n) (hmn n) (hn4 n) (hEn n)).sub (hA2 q hmq hq4 hEq)).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro z
      simpa only [v12_actualCoulombA, ← Complex.ofReal_sub, Complex.norm_real,
        PiLp.sub_apply] using PiLp.norm_apply_le
          (v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z) j
  have ht : Tendsto (fun n => (eLpNorm
      (fun z => v12_actualCoulombA (qn n) j z-v12_actualCoulombA q j z) 2 ν).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun n => ENNReal.toReal_nonneg)
      (fun n => ENNReal.toReal_mono (hAd n).eLpNorm_ne_top (hb n)) hAlim
  exact v12_raw_L2_drift_L1_limit ν (fun n => v12_actualCoulombA (qn n) j)
    (v12_actualCoulombA q j) qn q (fun n => hA2 (qn n) (hmn n) (hn4 n) (hEn n))
    (hA2 q hmq hq4 hEq) (hn2 R) (hq2 R) ht (hlim R)

#print axioms v12_raw_L2_drift_L1_limit
#print axioms v12_actual_Coulomb_drift_local_L1_limit
end SMScattering.W20Full
