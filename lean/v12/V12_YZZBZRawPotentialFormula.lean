import lean.v12.V12_YZZBUOriginalSourceBudgets

/-! The original V formula on a closed time slab, using its actual A0 L2
class. No continuous representative of A0 or V is assumed. Original spatial
Riesz sections of A0 are proved in YSFBOriginalTemporalSlices. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_originalReconstructedPotential
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (z : V12Spacetime) : ℂ :=
  -v12_actualTemporalCoulombL2 a b q hq z +
    ((‖v12_spacetimeHodge q z‖^2 : ℝ) : ℂ) - (2 : ℂ) * ((‖q z‖^2 : ℝ) : ℂ)

theorem v12_originalReconstructedPotential_extension_ae
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
    (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    v12_originalReconstructedPotential a b q hq =ᵐ[v12_slab_measure a b]
      v12_actualPotentialL2Class hHLS a b (v12_smoothSlabExtension a b q)
        (v12_smoothSlabExtension_stronglyMeasurable a b q hc)
        (v12_smoothSlabExtension_memLp a b q 4 hq) M
        (v12_smoothSlabExtension_energy a b q M hE) := by
  exact v12_original_V_extended_representative hHLS a b q hc hq M
    (v12_smoothSlabExtension_energy a b q M hE)
    (v12_actualTemporalCoulombL2 a b q hq) (v12_originalReconstructedPotential a b q hq)
    Filter.EventuallyEq.rfl (fun _ => rfl)

#print axioms v12_originalReconstructedPotential_extension_ae
end SMScattering.W20Full
