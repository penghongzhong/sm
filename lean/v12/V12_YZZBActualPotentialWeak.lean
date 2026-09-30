import lean.v12.V12_YSFActualTemporalCoulomb
import lean.v12.V12_YSHNormSquaredWeakClosure
import lean.v12.V12_YZYHodgeStrongLocal

/-! The full actual V=-A0+|A|^2-2m weak limit. The Hodge L4 budget and
local strong convergence are derived from the same Q sequence. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_Hodge_memLp4 (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (q : V12Spacetime → V12Field) (hmq : StronglyMeasurable q)
    (hq4 : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    MemLp (v12_spacetimeHodge q) 4 (v12_slab_measure a b) := by
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  exact (hH a b q hmq hq4 (ENNReal.ofReal M) (by finiteness) hEq).1

noncomputable def v12_actualPotentialL2Class (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (q : V12Spacetime → V12Field) (hmq : StronglyMeasurable q)
    (hq4 : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    Lp ℂ 2 (v12_slab_measure a b) :=
  -v12_actualTemporalCoulombL2 a b q hq4 +
    v12_normSqL2Class (v12_slab_measure a b) (v12_spacetimeHodge q)
      (v12_actual_Hodge_memLp4 hHLS a b q hmq hq4 M hEq) -
    (2 : ℂ) • v12_massComplexL2Class (v12_slab_measure a b) q hq4

theorem v12_actualPotential_weak_L2_limit
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
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hZq : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b) →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_actualPotentialL2Class hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n)))
        atTop (𝓝 (φ (v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq))) := by
  let μ := v12_slab_measure a b
  let hnA := fun n => v12_actual_Hodge_memLp4 hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n)
  let hqA := v12_actual_Hodge_memLp4 hHLS a b q hmq hq4 M hEq
  have hnA2 : ∀ R n, MemLp (v12_spacetimeHodge (qn n)) 2 (μ.restrict (v12_spatial_cylinder R)) := by
    intro R n
    exact ((hnA n).restrict (v12_spatial_cylinder R)).mono_exponent (by norm_num)
  have hqA2 : ∀ R, MemLp (v12_spacetimeHodge q) 2 (μ.restrict (v12_spatial_cylinder R)) := by
    intro R
    exact (hqA.restrict (v12_spatial_cylinder R)).mono_exponent (by norm_num)
  have hAlim := fun R => (v12_actual_Hodge_local_L2_limit hHLS a b R qn q hmn hmq
    hn4 hq4 hn2 hq2 hlim M hM hEn hEq Z hZ hZq).2
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  have hAb : ∀ n, eLpNorm (v12_spacetimeHodge (qn n)) 4 μ ≤ C*ENNReal.ofReal M*Z := by
    intro n
    exact ((hH a b (qn n) (hmn n) (hn4 n) (ENNReal.ofReal M) (by finiteness) (hEn n)).2).trans
      (mul_le_mul' le_rfl (hZq n))
  have hsq := v12_L2_integral_weak_to_dual μ
    (fun n => v12_normSqL2Class μ (v12_spacetimeHodge (qn n)) (hnA n))
    (v12_normSqL2Class μ (v12_spacetimeHodge q) hqA)
    (v12_normSq_weak_L2_limit a b (fun n => v12_spacetimeHodge (qn n)) (v12_spacetimeHodge q)
      hnA hqA hnA2 hqA2 hAlim (C*ENNReal.ofReal M*Z) (by finiteness) hAb)
  intro φ
  have h0 := v12_actualTemporalCoulomb_weak_L2_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hZq φ
  have hm := v12_actualMassL2_dual_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hZq φ
  simpa only [v12_actualPotentialL2Class, map_sub, map_add, map_neg, map_smul] using
    ((h0.neg).add (hsq φ)).sub (hm.const_smul (2 : ℂ))

theorem v12_actualPotential_L2_budget (hHLS : V12ExternalHLS2D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ) (q : V12Spacetime → V12Field)
      (hmq : StronglyMeasurable q) (hq4 : MemLp q 4 (v12_slab_measure a b))
      (M : ℝ) (hM : 0 ≤ M)
      (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
      (Z : ℝ≥0∞) (hZ : Z ≠ ∞), eLpNorm q 4 (v12_slab_measure a b) ≤ Z →
      ‖v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq‖ ≤ (24+C*M^2)*Z.toReal^2 := by
  obtain ⟨C, hC, hH⟩ := v12_actual_hodge_spacetime_MZ hHLS
  refine ⟨C.toReal^2, sq_nonneg _, ?_⟩
  intro a b q hmq hq4 M hM hEq Z hZ hb
  let μ := v12_slab_measure a b
  have h0 := v12_actualTemporalCoulomb_L2_budget a b q hq4 Z hZ hb
  have hm : ‖v12_massComplexL2Class μ q hq4‖ ≤ 2*Z.toReal^2 := by
    apply (norm_add_le _ _).trans
    simpa only [two_mul] using add_le_add
      (v12_tensorL2Class_budget μ 0 0 q hq4 Z hZ hb)
      (v12_tensorL2Class_budget μ 1 1 q hq4 Z hZ hb)
  have hAb : eLpNorm (v12_spacetimeHodge q) 4 μ ≤ C*ENNReal.ofReal M*Z :=
    ((hH a b q hmq hq4 (ENNReal.ofReal M) (by finiteness) hEq).2).trans
      (mul_le_mul' le_rfl hb)
  have hs := v12_normSqL2Class_budget μ (v12_spacetimeHodge q)
    (v12_actual_Hodge_memLp4 hHLS a b q hmq hq4 M hEq)
    (C*ENNReal.ofReal M*Z) (by finiteness) hAb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, mul_pow] at hs
  unfold v12_actualPotentialL2Class
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_neg, norm_smul, Complex.norm_ofNat]
  nlinarith

#print axioms v12_actualPotential_L2_budget

#print axioms v12_actual_Hodge_memLp4
#print axioms v12_actualPotential_weak_L2_limit
end SMScattering.W20Full
