import lean.v12.V12_YNonlinearLocalProducts
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Convert the proved integral-test weak limit to every continuous linear
functional. This justifies application of the actual Fourier Riesz operator. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology

theorem v12_L2_integral_weak_to_dual
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (fn : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ)
    (hw : ∀ ψ : Lp ℂ 2 μ,
      Tendsto (fun n => ∫ z, fn n z * ψ z ∂μ) atTop (𝓝 (∫ z, f z * ψ z ∂μ))) :
    ∀ φ : Lp ℂ 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => φ (fn n)) atTop (𝓝 (φ f)) := by
  intro φ
  let g := (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm φ
  let ψ := Complex.conjCLE.toContinuousLinearMap.compLp g
  have he (q : Lp ℂ 2 μ) : φ q = ∫ z, q z * ψ z ∂μ := by
    rw [← InnerProductSpace.toDual_symm_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLp g] with z hz
    change ψ z = star (g z) at hz
    simp only [RCLike.inner_apply, g, hz, Complex.star_def]
  simpa only [← he] using hw ψ

theorem v12_L2_dual_weak_to_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (fn : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ)
    (hw : ∀ φ : Lp ℂ 2 μ →L[ℂ] ℂ,
      Tendsto (fun n => φ (fn n)) atTop (𝓝 (φ f))) :
    ∀ ψ : Lp ℂ 2 μ,
      Tendsto (fun n => ∫ z, fn n z * ψ z ∂μ) atTop (𝓝 (∫ z, f z * ψ z ∂μ)) := by
  intro ψ
  let B := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  have h := hw (B.flip ψ)
  simpa only [B, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply'] using h

#print axioms v12_L2_integral_weak_to_dual
#print axioms v12_L2_dual_weak_to_integral
end SMScattering.W20Full
