import lean.v12.V12_YZZKActualCompactPDE
import lean.v12.V12_YZZGROriginalDistributionTests
import lean.v12.V12_YZZBZRawPotentialFormula

/-! Original distributional PDE is preserved by the concrete closed-slab
extension, with the source identified through the original reconstruction
formula. No A0/V continuity, global Q measurability, or derived integral
identity is an additional premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_originalScalarSource
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (j : Fin 2) (z : V12Spacetime) : ℂ :=
  v12_originalReconstructedPotential a b q hq z * q z j +
    v12_WDensity (q z) * star (q z j)

theorem v12_originalScalarSource_extension_ae
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
    (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) (j : Fin 2) :
    v12_originalScalarSource a b q hq j =ᵐ[v12_slab_measure a b]
      v12_actualScalarZeroOrder hHLS a b (v12_smoothSlabExtension a b q)
        (v12_smoothSlabExtension_stronglyMeasurable a b q hc)
        (v12_smoothSlabExtension_memLp a b q 4 hq) M
        (v12_smoothSlabExtension_energy a b q M hE) j := by
  filter_upwards [v12_originalReconstructedPotential_extension_ae hHLS a b q hc hq M hE,
    v12_smoothSlabExtension_ae a b q] with z hv he
  simp only [v12_originalScalarSource, v12_actualScalarZeroOrder, he, hv]

theorem v12_original_distributional_PDE_extension
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
    (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (j : Fin 2) (vt e₀ e₁ : V12Spacetime)
    (hPDE : V12OriginalScalarDistributionalPDE a b (fun z => q z j)
      (v12_actualCoulombA q) (v12_originalScalarSource a b q hq j) vt e₀ e₁) :
    V12OriginalScalarDistributionalPDE a b
      (fun z => v12_smoothSlabExtension a b q z j)
      (v12_actualCoulombA (v12_smoothSlabExtension a b q))
      (v12_actualScalarZeroOrder hHLS a b (v12_smoothSlabExtension a b q)
        (v12_smoothSlabExtension_stronglyMeasurable a b q hc)
        (v12_smoothSlabExtension_memLp a b q 4 hq) M
        (v12_smoothSlabExtension_energy a b q M hE) j) vt e₀ e₁ := by
  let ext := v12_smoothSlabExtension a b q
  let μ := v12_slab_measure a b
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hecomp : Set.EqOn (fun z => ext z j) (fun z => q z j) U :=
    fun z hz => congrArg (fun v : V12Field => v j) (v12_smoothSlabExtension_eqOn_interior a b q hz)
  have hd := v12_open_eqOn_fderiv U hU _ _ hecomp
  have hm := v12_smoothSlabExtension_stronglyMeasurable a b q hc
  have he4 := v12_smoothSlabExtension_memLp a b q 4 hq
  have heE := v12_smoothSlabExtension_energy a b q M hE
  intro ψ hψ hcψ hs
  have hpair (χ : V12Spacetime → ℂ) :
      (∫ z, ext z j * χ z ∂μ) = ∫ z, q z j * χ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [v12_smoothSlabExtension_ae a b q] with z hz
    change ext z = q z at hz
    rw [hz]
  have hr :
      (fun z => ((2 * Complex.I) *
        (v12_actualCoulombA ext 0 z * fderiv ℝ (fun x => ext x j) z e₀ +
         v12_actualCoulombA ext 1 z * fderiv ℝ (fun x => ext x j) z e₁) +
        v12_actualScalarZeroOrder hHLS a b ext hm he4 M heE j z) * ψ z) =ᵐ[μ]
      (fun z => ((2 * Complex.I) *
        (v12_actualCoulombA q 0 z * fderiv ℝ (fun x => q x j) z e₀ +
         v12_actualCoulombA q 1 z * fderiv ℝ (fun x => q x j) z e₁) +
        v12_originalScalarSource a b q hq j z) * ψ z) := by
    filter_upwards [v12_originalScalarSource_extension_ae hHLS a b q hc hq M hE j] with z hg
    by_cases hz : z ∈ U
    · rw [hd hz, v12_smoothSlabExtension_A_eqOn_interior a b q 0 hz,
        v12_smoothSlabExtension_A_eqOn_interior a b q 1 hz, ← hg]
    · have hzero : ψ z = 0 := by
        by_contra hne
        exact hz (hs (subset_tsupport ψ hne))
      rw [hzero, mul_zero, mul_zero]
  rw [integral_congr_ae hr]
  dsimp only [ext, μ] at hpair
  simpa only [hpair, μ] using hPDE ψ hψ hcψ hs

#print axioms v12_originalScalarSource_extension_ae
#print axioms v12_original_distributional_PDE_extension
end SMScattering.W20Full
