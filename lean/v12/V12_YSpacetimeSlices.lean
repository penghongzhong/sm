import lean.v12.V12_SourceProducts
import Mathlib.MeasureTheory.Integral.Prod

/-!
Fubini leaves for the actual spacetime source. These prove almost-everywhere
spatial Lp sections and their scalar integral budget. They do not assert
Bochner measurability of the Lp-valued section map or every-time membership.
-/

set_option autoImplicit false

namespace SMScattering.W20Full

open MeasureTheory
open scoped ENNReal

theorem v12_spacetime_memLp_slices
    (μ : Measure ℝ) [SFinite μ] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    (q : ℝ × V12Spatial → V12Field)
    (hq : MemLp q p (μ.prod (volume : Measure V12Spatial))) :
    ∀ᵐ t ∂μ, MemLp (fun y => q (t,y)) p (volume : Measure V12Spatial) := by
  have hi := hq.integrable_norm_rpow hp0 hp_top
  filter_upwards [hi.prod_right_ae, hq.aestronglyMeasurable.prodMk_left] with t ht hm
  exact (integrable_norm_rpow_iff hm hp0 hp_top).mp ht

theorem v12_spacetime_slice_power_integrable
    (μ : Measure ℝ) [SFinite μ] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    (q : ℝ × V12Spatial → V12Field)
    (hq : MemLp q p (μ.prod (volume : Measure V12Spatial))) :
    Integrable (fun t => ∫ y : V12Spatial, ‖q (t,y)‖ ^ p.toReal) μ :=
  (hq.integrable_norm_rpow hp0 hp_top).integral_prod_left

theorem v12_spacetime_slice_power_integral
    (μ : Measure ℝ) [SFinite μ] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    (q : ℝ × V12Spatial → V12Field)
    (hq : MemLp q p (μ.prod (volume : Measure V12Spatial))) :
    (∫ z, ‖q z‖ ^ p.toReal ∂(μ.prod (volume : Measure V12Spatial))) =
      ∫ t, (∫ y : V12Spatial, ‖q (t,y)‖ ^ p.toReal) ∂μ :=
  integral_prod _ (hq.integrable_norm_rpow hp0 hp_top)

#print axioms v12_spacetime_memLp_slices
#print axioms v12_spacetime_slice_power_integrable
#print axioms v12_spacetime_slice_power_integral

end SMScattering.W20Full
