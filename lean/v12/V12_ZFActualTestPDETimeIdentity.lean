import lean.v12.V12_ZDCompactTestTimeIdentity
import lean.v12.V12_ZERawSourceRepresentatives

/-!
The finite compact-test time identity with the SAME Lp source. Raw PDE,
smoothness and representative equalities are the inputs. Source integrability,
spatial integration by parts and the tested FTC are conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open MeasureTheory LineDeriv Laplacian
open scoped ContDiff

noncomputable def v12_rawDivergenceRHS
    (q : V12Spatial → V12Field) (f : Fin 2 → V12Spatial → V12Field)
    (g : V12Spatial → V12Field) (y : V12Spatial) : V12Field :=
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  Complex.I • (fderiv ℝ (fun z => fderiv ℝ q z (e 0)) y (e 0) +
    fderiv ℝ (fun z => fderiv ℝ q z (e 1)) y (e 1)) +
  (2 : ℂ) • fderiv ℝ (f 0) y (e 0) +
  (2 : ℂ) • fderiv ℝ (f 1) y (e 1) + (-Complex.I) • g y

theorem v12_actual_test_pde_time_identity
    (a b : ℝ) (ψ : SchwartzMap V12Spatial ℂ)
    (hc : HasCompactSupport (ψ : V12Spatial → ℂ))
    (q dq g : ℝ → V12Spatial → V12Field)
    (f : Fin 2 → ℝ → V12Spatial → V12Field)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hqcont : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (hdqcont : ContinuousOn (Function.uncurry dq) (Set.Icc a b ×ˢ Set.univ))
    (hder : ∀ τ ∈ Set.Ioo a b, ∀ y, HasDerivAt (fun σ => q σ y) (dq τ y) τ)
    (hPDE : ∀ τ ∈ Set.Ioo a b, ∀ y,
      dq τ y = v12_rawDivergenceRHS (q τ) (fun j => f j τ) (g τ) y)
    (hq : ∀ τ ∈ Set.Ioo a b, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q τ))
    (hf : ∀ τ ∈ Set.Ioo a b, ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j τ))
    (hg : ∀ τ ∈ Set.Ioo a b, Continuous (g τ))
    (hQ : ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (Q τ : V12Spatial → V12Field) =ᵐ[volume] q τ)
    (hF : ∀ j, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (F j τ : V12Spatial → V12Field) =ᵐ[volume] f j τ)
    (hG : ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (G τ : V12Spatial → V12Field) =ᵐ[volume] g τ)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    let S := v12_testSourceFromLpKernels ((Δ ψ).toLp 2 (volume : Measure V12Spatial))
      (fun j => (∂_{e j} ψ).toLp 2 (volume : Measure V12Spatial))
      (ψ.toLp 4 (volume : Measure V12Spatial)) Q F G
    IntervalIntegrable S volume s t ∧
      (∫ y : V12Spatial, ψ y • q t y) - (∫ y : V12Spatial, ψ y • q s y) =
        ∫ τ in s..t, S τ := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let S := v12_testSourceFromLpKernels ((Δ ψ).toLp 2 (volume : Measure V12Spatial))
    (fun j => (∂_{e j} ψ).toLp 2 (volume : Measure V12Spatial))
    (ψ.toLp 4 (volume : Measure V12Spatial)) Q F G
  let d : ℝ → V12Field := fun τ => ∫ y : V12Spatial, ψ y • dq τ y
  have hsub : (volume : Measure ℝ).restrict (Set.Ioo s t) ≤
      (volume : Measure ℝ).restrict (Set.Icc a b) := by
    apply Measure.restrict_mono _ le_rfl
    intro τ hτ
    exact ⟨hs.1.trans hτ.1.le, hτ.2.le.trans ht.2⟩
  have heq : d =ᵐ[(volume : Measure ℝ).restrict (Set.Ioo s t)] S := by
    filter_upwards [Filter.Eventually.filter_mono (ae_mono hsub) hQ,
      Filter.Eventually.filter_mono (ae_mono hsub) (ae_all_iff.mpr hF),
      Filter.Eventually.filter_mono (ae_mono hsub) hG, ae_restrict_mem measurableSet_Ioo] with τ hQτ hFτ hGτ hτ
    have hτab : τ ∈ Set.Ioo a b := ⟨hs.1.trans_lt hτ.1, hτ.2.trans_le ht.2⟩
    exact (v12_testSource_eq_raw_pde_derivative ψ hc Q F G τ
      (q τ) (dq τ) (g τ) (fun j => f j τ) hQτ hFτ hGτ
      (hq τ hτab) (hf τ hτab) (hg τ hτab) (hPDE τ hτab)).symm
  have heq' : d =ᵐ[(volume : Measure ℝ).restrict (Set.uIoc s t)] S := by
    rw [Set.uIoc_of_le hst, ← restrict_Ioo_eq_restrict_Ioc]
    exact heq
  have hdcont : ContinuousOn d (Set.Icc a b) :=
    v12_compact_pairing_continuousOn (Set.Icc a b) ψ ψ.continuous hc dq hdqcont
  have hdint : IntervalIntegrable d volume s t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hst]
    exact hdcont.mono (fun τ hτ => ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩)
  have hsint : IntervalIntegrable S volume s t :=
    hdint.congr_ae heq'
  refine ⟨hsint, ?_⟩
  calc
    (∫ y : V12Spatial, ψ y • q t y) - (∫ y : V12Spatial, ψ y • q s y) =
        ∫ τ in s..t, d τ :=
      v12_compact_pairing_time_identity a b ψ ψ.continuous hc q dq
        hqcont hdqcont hder hs ht hst
    _ = ∫ τ in s..t, S τ := intervalIntegral.integral_congr_ae_restrict heq'

#print axioms v12_actual_test_pde_time_identity

end SMScattering.W20Full
