import lean.v12.V12_YWCoulombDriftBudget
import lean.v12.V12_YZZHOriginalCompactPDE
import lean.v12.V12_YZZJActualZeroOrderTests

/-! Actual reconstructed zero-order source in the original compact PDE.
Its membership, local integrability and testing are derived from Q L4,
actual A0/Hodge/mass reconstruction and standard Holder. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_actualScalarZeroOrder
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hmq : StronglyMeasurable q) (hq4 : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (j : Fin 2) (z : V12Spacetime) : ℂ :=
  v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq z * q z j +
    v12_WDensity (q z) * star (q z j)

theorem v12_actualScalarZeroOrder_memLp
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hmq : StronglyMeasurable q) (hq4 : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) (j : Fin 2) :
    MemLp (v12_actualScalarZeroOrder hHLS a b q hmq hq4 M hEq j)
      ((4 : ℝ≥0∞)/3) (v12_slab_measure a b) := by
  let μ := v12_slab_measure a b
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) 4 ((4 : ℝ≥0∞)/3) :=
    v12_holderTriple_two_four_fourThirds
  have hqj : MemLp (fun z => q z j) 4 μ :=
    (v12_raw_component_eLpNorm_le μ 4 q hq4.aestronglyMeasurable j).trans_lt hq4
  exact ((Lp.memLp (v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq)).mul hqj).add
    ((v12_actual_W_mass_L2_budgets μ q hq4).1.mul hqj.star)

theorem v12_actual_scalar_compact_PDE_identity
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hmq : StronglyMeasurable q) (hq4 : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (j : Fin 2) (ψ : V12Spacetime → ℂ) (vt e₀ e₁ : V12Spacetime)
    (hqSmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => q z j) (Prod.fst ⁻¹' Set.Ioo a b))
    (hASmooth : ∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (v12_actualCoulombA q k) (Prod.fst ⁻¹' Set.Ioo a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b)
    (hdiv : ∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (v12_actualCoulombA q 0) z e₀ +
      fderiv ℝ (v12_actualCoulombA q 1) z e₁ = 0)
    (hPDE : ∀ᵐ z ∂v12_slab_measure a b, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      Complex.I * fderiv ℝ (fun x => q x j) z vt +
      (fderiv ℝ (fun x => fderiv ℝ (fun y => q y j) x e₀) z e₀ +
       fderiv ℝ (fun x => fderiv ℝ (fun y => q y j) x e₁) z e₁) =
      (2 * Complex.I) *
        (v12_actualCoulombA q 0 z * fderiv ℝ (fun x => q x j) z e₀ +
         v12_actualCoulombA q 1 z * fderiv ℝ (fun x => q x j) z e₁) +
      v12_actualScalarZeroOrder hHLS a b q hmq hq4 M hEq j z) :
    -Complex.I * (∫ z, q z j * fderiv ℝ ψ z vt ∂v12_slab_measure a b) +
      ((∫ z, q z j * fderiv ℝ (fun x => fderiv ℝ ψ x e₀) z e₀ ∂v12_slab_measure a b) +
       (∫ z, q z j * fderiv ℝ (fun x => fderiv ℝ ψ x e₁) z e₁ ∂v12_slab_measure a b)) =
    -(2 * Complex.I) *
      ((∫ z, (v12_actualCoulombA q 0 z * q z j) * fderiv ℝ ψ z e₀ ∂v12_slab_measure a b) +
       (∫ z, (v12_actualCoulombA q 1 z * q z j) * fderiv ℝ ψ z e₁ ∂v12_slab_measure a b)) +
      ∫ z, v12_actualScalarZeroOrder hHLS a b q hmq hq4 M hEq j z * ψ z
        ∂v12_slab_measure a b := by
  exact v12_original_scalar_compact_PDE a b (fun z => q z j) (v12_actualCoulombA q)
    (v12_actualScalarZeroOrder hHLS a b q hmq hq4 M hEq j) ψ vt e₀ e₁ hqSmooth hASmooth
    (v12_actualScalarZeroOrder_memLp hHLS a b q hmq hq4 M hEq j) hψ hc hs hdiv hPDE

#print axioms v12_actualScalarZeroOrder_memLp
#print axioms v12_actual_scalar_compact_PDE_identity
end SMScattering.W20Full
