import lean.v12.V12_YZZBSActualPotentialReality
import lean.v12.V12_YSFCOriginalTemporalRepresentative
import lean.v12.V12_YWTSlabDerivativePreservation

/-! The original smooth potential is the same L2 coefficient after zero
extension of Q. Its L2 membership and budget follow from the actual Hodge
and Riesz construction; they are not source hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_actualTemporalCoulomb_congr_ae
    (a b : ℝ) (q r : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (hr : MemLp r 4 (v12_slab_measure a b))
    (he : q =ᵐ[v12_slab_measure a b] r) :
    v12_actualTemporalCoulombL2 a b q hq = v12_actualTemporalCoulombL2 a b r hr := by
  have hS (j k : Fin 2) :
      v12_SL2Class (v12_slab_measure a b) j k q hq =
      v12_SL2Class (v12_slab_measure a b) j k r hr := by
    apply Lp.ext_iff.mpr
    filter_upwards [v12_SL2Class_ae (v12_slab_measure a b) j k q hq,
      v12_SL2Class_ae (v12_slab_measure a b) j k r hr, he] with z hqz hrz hz
    rw [hqz, hrz, hz]
  have hm : v12_massComplexL2Class (v12_slab_measure a b) q hq =
      v12_massComplexL2Class (v12_slab_measure a b) r hr := by
    apply Lp.ext_iff.mpr
    filter_upwards [v12_massComplexL2Class_ae (v12_slab_measure a b) q hq,
      v12_massComplexL2Class_ae (v12_slab_measure a b) r hr, he] with z hqz hrz hz
    rw [hqz, hrz, hz]
  simp only [v12_actualTemporalCoulombL2_eq, hS, hm]

theorem v12_original_V_extended_representative
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
    (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => v12_smoothSlabExtension a b q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (A0 V : V12Spacetime → ℂ)
    (hA0 : A0 =ᵐ[v12_slab_measure a b] v12_actualTemporalCoulombL2 a b q hq)
    (hV : ∀ z, V z = -A0 z + ((‖v12_spacetimeHodge q z‖^2 : ℝ) : ℂ) -
      (2 : ℂ) * ((‖q z‖^2 : ℝ) : ℂ)) :
    V =ᵐ[v12_slab_measure a b]
      v12_actualPotentialL2Class hHLS a b (v12_smoothSlabExtension a b q)
        (v12_smoothSlabExtension_stronglyMeasurable a b q hc)
        (v12_smoothSlabExtension_memLp a b q 4 hq) M hE := by
  have hAeq := v12_actualTemporalCoulomb_congr_ae a b _ q
    (v12_smoothSlabExtension_memLp a b q 4 hq) hq (v12_smoothSlabExtension_ae a b q)
  filter_upwards [v12_actualPotentialL2Class_ae hHLS a b _
      (v12_smoothSlabExtension_stronglyMeasurable a b q hc)
      (v12_smoothSlabExtension_memLp a b q 4 hq) M hE,
    hA0, v12_smoothSlabExtension_Hodge_ae a b q, v12_smoothSlabExtension_ae a b q]
    with z hv ha hh hqz
  rw [hv, hAeq, hh, hqz, hV, ha]

theorem v12_original_V_memLp_of_representative
    (μ : Measure V12Spacetime) (V : V12Spacetime → ℂ) (F : Lp ℂ 2 μ)
    (he : V =ᵐ[μ] F) : MemLp V 2 μ :=
  (Lp.memLp F).ae_eq he.symm

theorem v12_original_V_budget_of_representative
    (μ : Measure V12Spacetime) (V : V12Spacetime → ℂ) (F : Lp ℂ 2 μ)
    (he : V =ᵐ[μ] F) (B : ℝ) (hb : ‖F‖ ≤ B) :
    (eLpNorm V 2 μ).toReal ≤ B := by
  have hm := v12_original_V_memLp_of_representative μ V F he
  have heq : hm.toLp V = F := Lp.ext_iff.mpr (hm.coeFn_toLp.trans he)
  rw [← Lp.norm_toLp V hm, heq]
  exact hb

#print axioms v12_actualTemporalCoulomb_congr_ae
#print axioms v12_original_V_extended_representative
#print axioms v12_original_V_budget_of_representative
end SMScattering.W20Full
