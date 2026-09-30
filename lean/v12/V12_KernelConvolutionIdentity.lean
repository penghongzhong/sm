import lean.v12.V12_FrequencyTightnessLimit

/-! Explicit Lp representatives first, Schwartz specialization second.
Splitting these identities avoids one large kernel definitional-equality
check containing both Lp and Schwartz structures. No assumptions are added
to the final Schwartz convolution identity. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped ENNReal

/-- Replace the two Lp representatives by any equal-a.e. concrete functions
under the actual convolution integral. -/
theorem v12_L2ConvolutionRep_eq_integral_of_ae
    (k : V12ScalarL2) (f : V12SpatialL2)
    (K : V12Spatial → ℂ) (F : V12Spatial → V12Field)
    (hk : (k : V12Spatial → ℂ) =ᵐ[volume] K)
    (hf : (f : V12Spatial → V12Field) =ᵐ[volume] F)
    (x : V12Spatial) :
    v12_L2ConvolutionRep k f x = ∫ y : V12Spatial, K (x - y) • F y := by
  have hkx :=
    (v12_subLeft_measurePreserving x).quasiMeasurePreserving.ae hk
  calc
    v12_L2ConvolutionRep k f x = ∫ y : V12Spatial, k (x - y) • f y :=
      v12_L2ConvolutionRep_eq_integral k f x
    _ = ∫ y : V12Spatial, K (x - y) • F y := by
      apply integral_congr_ae
      filter_upwards [hkx, hf] with y hky hfy
      have hky' : k (x - y) = K (x - y) := by
        simpa only [v12_subLeftFamily_apply] using hky
      rw [hky', hfy]

/-- The scalar-vector Schwartz convolution in the same swapped integral order. -/
theorem v12_schwartzConvolution_apply_eq_integral
    (k : SchwartzMap V12Spatial ℂ)
    (f : SchwartzMap V12Spatial V12Field) (x : V12Spatial) :
    SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] V12Field →L[ℂ] V12Field) k f x =
      ∫ y : V12Spatial, k (x - y) • f y := by
  rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_eq_swap]
  rfl

/-- General Schwartz identity, now a composition of two already checked
integral identities, without unfolding both structures in the same proof. -/
theorem v12_schwartzKernel_rep_eq_schwartzConvolution
    (k : SchwartzMap V12Spatial ℂ)
    (f : SchwartzMap V12Spatial V12Field) (x : V12Spatial) :
    v12_L2ConvolutionRep (k.toLp 2) (f.toLp 2) x =
      SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] V12Field →L[ℂ] V12Field) k f x := by
  have h := v12_L2ConvolutionRep_eq_integral_of_ae
    (k.toLp 2 (volume : Measure V12Spatial))
    (f.toLp 2 (volume : Measure V12Spatial)) k f
    (k.coeFn_toLp 2 (volume : Measure V12Spatial))
    (f.coeFn_toLp 2 (volume : Measure V12Spatial)) x
  exact h.trans (v12_schwartzConvolution_apply_eq_integral k f x).symm

#print axioms v12_L2ConvolutionRep_eq_integral_of_ae
#print axioms v12_schwartzConvolution_apply_eq_integral
#print axioms v12_schwartzKernel_rep_eq_schwartzConvolution

end SMScattering.W20Full
