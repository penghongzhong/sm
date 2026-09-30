import lean.v12.V12_YZXHodgeApproximationError
import lean.v12.V12_YXZYoungCurvatureApplication
import lean.v12.V12_YXApproximationLimit

/-! Actual local Hodge strong convergence from the original Q sequence.
Near density convergence and far error are derived in preceding modules. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_Hodge_local_fourThirds_limit
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (R : ℕ)
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
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    Tendsto (fun n => (eLpNorm (fun z => v12_spacetimeHodge (qn n) z - v12_spacetimeHodge q z)
      ((4 : ℝ≥0∞) / 3) ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal)
      atTop (𝓝 0) := by
  let ν := (v12_slab_measure a b).restrict (v12_spatial_cylinder R)
  let p : ℝ≥0∞ := 4/3
  let S : ℕ → ℕ := fun k => 2*(R+1)+k
  let L : ℕ → ℝ := fun k => (S k : ℝ)+1
  let f := fun n z => v12_spacetimeHodge (qn n) z - v12_spacetimeHodge q z
  let g := fun k n => v12_spacetimeNearHodge (((R : ℝ)+1)+L k)
    (v12_curvatureCutoffDifference (L k) (qn n) q)
  have hp : p ≤ 4 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  have hAq := (hH a b q hmq hq4 (ENNReal.ofReal M) (by finiteness) hEq).1
  have hAn := fun n => (hH a b (qn n) (hmn n) (hn4 n) (ENNReal.ofReal M) (by finiteness) (hEn n)).1
  have hf : ∀ n, MemLp (f n) p ν := by
    intro n
    exact (((hAn n).sub hAq).restrict (v12_spatial_cylinder R)).mono_exponent hp
  have hg : ∀ k, (∀ n, MemLp (g k n) p (v12_slab_measure a b)) ∧
      Tendsto (fun n => (eLpNorm (g k n) p (v12_slab_measure a b)).toReal) atTop (𝓝 0) := by
    intro k
    exact v12_actual_curvature_near_spacetime_limit a b (S k) (((R : ℝ)+1)+L k)
      qn q hmn hmq (hn2 (S k)) (hq2 (S k)) (hlim (S k)) M hM hEn hEq
  let F := fun n => (hf n).toLp (f n)
  let G := fun k n => ((hg k).1 n |>.restrict (v12_spatial_cylinder R)).toLp (g k n)
  have hG : ∀ k, Tendsto (G k) atTop (𝓝 0) := by
    intro k
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ (hg k).2
    intro n
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono ((hg k).1 n).eLpNorm_ne_top
      (eLpNorm_mono_measure (g k n) Measure.restrict_le_self)
  let D : ℝ≥0∞ := (ν Set.univ)^p.toReal⁻¹
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top ν Set.univ)
  let δ := fun k => D.toReal * ((Real.pi*L k)⁻¹*(4*M^2))
  have hL : ∀ k, 0 < L k := by intro k; dsimp [L]; positivity
  have hRL : ∀ k, 2*((R : ℝ)+1) ≤ L k := by
    intro k
    dsimp [L, S]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have herr : ∀ k n, ‖F n - G k n‖ ≤ δ k := by
    intro k n
    have hae : ((F n - G k n : Lp V12Spatial p ν) : V12Spacetime → V12Spatial) =ᵐ[ν]
        v12_HodgeApproxError ((R : ℝ)+1) (L k) (qn n) q := by
      apply (Lp.coeFn_sub _ _).trans
      exact (hf n).coeFn_toLp.sub (((hg k).1 n).restrict (v12_spatial_cylinder R)).coeFn_toLp
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    have he := v12_HodgeApproxError_Lp_bound hHLS a b R (L k) (hL k) (hRL k)
      (qn n) q (hmn n) hmq (hn4 n) hq4 M hM (hEn n) hEq p
    have hr := ENNReal.toReal_mono (by change D * ENNReal.ofReal _ ≠ ∞; finiteness) he
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by positivity : 0 ≤ (Real.pi*L k)⁻¹*(4*M^2))] using hr
  have hLtop : Tendsto L atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ)) _ tendsto_natCast_atTop_atTop
    intro k
    dsimp [L, S]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) R]
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp (Filter.Tendsto.const_mul_atTop Real.pi_pos hLtop)
    simpa only [mul_zero, zero_mul] using (hi.mul_const (4*M^2)).const_mul D.toReal
  have hF := v12_limit_zero_from_uniform_approximants F G δ hδ hG herr
  have ht := hF.norm
  simpa only [F, Lp.norm_toLp, norm_zero] using ht

theorem v12_actual_Hodge_local_L2_limit
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (R : ℕ)
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
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞)
    (hZq : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z) :
    (∀ n, MemLp (fun z => v12_spacetimeHodge (qn n) z - v12_spacetimeHodge q z)
      2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) ∧
    Tendsto (fun n => (eLpNorm (fun z => v12_spacetimeHodge (qn n) z - v12_spacetimeHodge q z)
      2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
  let μ := v12_slab_measure a b
  let ν := μ.restrict (v12_spatial_cylinder R)
  let f := fun n z => v12_spacetimeHodge (qn n) z - v12_spacetimeHodge q z
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  have hAq := hH a b q hmq hq4 (ENNReal.ofReal M) (by finiteness) hEq
  have hAn := fun n => hH a b (qn n) (hmn n) (hn4 n)
    (ENNReal.ofReal M) (by finiteness) (hEn n)
  let D := C * ENNReal.ofReal M * Z + C * ENNReal.ofReal M * eLpNorm q 4 μ
  have hD : D ≠ ∞ := by dsimp [D, μ]; finiteness [hq4.eLpNorm_ne_top]
  have h4 : ∀ n, eLpNorm (f n) 4 ν ≤ D := by
    intro n
    apply (eLpNorm_mono_measure (f n) Measure.restrict_le_self).trans
    apply (eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 4)).trans
    apply add_le_add _ hAq.2
    exact (hAn n).2.trans (mul_le_mul' le_rfl (hZq n))
  have hp : (4 : ℝ≥0∞)/3 ≤ 4 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num
  have h43 : ∀ n, MemLp (f n) ((4 : ℝ≥0∞)/3) ν := by
    intro n
    have hm : MemLp (f n) 4 ν := (h4 n).trans_lt hD.lt_top
    exact hm.mono_exponent hp
  have ht := v12_actual_Hodge_local_fourThirds_limit hHLS a b R qn q hmn hmq
    hn4 hq4 hn2 hq2 hlim M hM hEn hEq
  exact v12_hodge_L2_limit_of_fourThirds_limit ν f h43 D hD h4 ht

#print axioms v12_actual_Hodge_local_L2_limit

#print axioms v12_actual_Hodge_local_fourThirds_limit
end SMScattering.W20Full
