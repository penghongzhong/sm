import lean.v12.V12_FrequencyTightnessLimit
import Mathlib.MeasureTheory.Measure.Prod

/-! Standard local-finiteness instances for the actual restricted product
Lebesgue slab. The noncomputable measure alias is unfolded in these proofs;
no measure property is an external or unproved interface. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
instance v12_slab_measure_locallyFinite (a b : ℝ) :
    IsLocallyFiniteMeasure (v12_slab_measure a b) := by
  unfold v12_slab_measure
  infer_instance
instance v12_slab_measure_finiteOnCompacts (a b : ℝ) :
    IsFiniteMeasureOnCompacts (v12_slab_measure a b) := by
  unfold v12_slab_measure
  infer_instance
#print axioms v12_slab_measure_locallyFinite
#print axioms v12_slab_measure_finiteOnCompacts
end SMScattering.W20Full
