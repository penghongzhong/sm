import lean.v12.V12_YWTSlabDerivativePreservation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Canonical time/spatial directions agree with the original curried
derivatives. These are chain-rule proofs, not coordinate-PDE interfaces. -/
set_option autoImplicit false
namespace SMScattering.W20Full

noncomputable def v12_timeDirection : V12Spacetime := (1,0)
noncomputable def v12_spatialDirection (j : Fin 2) : V12Spacetime :=
  (0, EuclideanSpace.basisFun (Fin 2) ℝ j)

theorem v12_joint_smooth_time_hasDerivAt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (f : V12Spacetime → E)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : V12Spatial) :
    HasDerivAt (fun s => f (s,x)) (deriv (fun s => f (s,x)) t) t := by
  have hU : IsOpen (Prod.fst ⁻¹' Set.Ioo a b : Set V12Spacetime) :=
    isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hd : DifferentiableAt ℝ f (t,x) :=
    (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ht)
  have hi : HasDerivAt (fun s : ℝ => (s,x)) (1,0) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const x t)
  exact (hd.hasFDerivAt.comp_hasDerivAt t hi).differentiableAt.hasDerivAt

theorem v12_joint_fderiv_spatial_slice
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : V12Spacetime → E) (t : ℝ) (x v : V12Spatial)
    (hf : DifferentiableAt ℝ f (t,x)) :
    fderiv ℝ f (t,x) (0,v) = fderiv ℝ (fun y => f (t,y)) x v := by
  have hi := (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hc := hf.hasFDerivAt.comp x hi
  have he := congrArg (fun L : V12Spatial →L[ℝ] E => L v) hc.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply] using he.symm

theorem v12_joint_fderiv_time_slice
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : V12Spacetime → E) (t : ℝ) (x : V12Spatial) (d : E)
    (hf : DifferentiableAt ℝ f (t,x))
    (hd : HasDerivAt (fun s => f (s,x)) d t) :
    fderiv ℝ f (t,x) v12_timeDirection = d := by
  have hi : HasDerivAt (fun s : ℝ => (s,x)) (1,0) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const x t)
  have hc := hf.hasFDerivAt.comp_hasDerivAt t hi
  exact hc.unique hd

theorem v12_joint_second_spatial_slice
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (f : V12Spacetime → E)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x v w : V12Spatial) :
    fderiv ℝ (fun z => fderiv ℝ f z (0,v)) (t,x) (0,w) =
      fderiv ℝ (fun y => fderiv ℝ (fun z => f (t,z)) y v) x w := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hdiff (y : V12Spatial) : DifferentiableAt ℝ f (t,y) :=
    (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ht)
  have hd := (hf.fderiv_of_isOpen hU (by simp)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : V12Spacetime => (0,v)) U)
  have hdif : DifferentiableAt ℝ (fun z => fderiv ℝ f z (0,v)) (t,x) :=
    (hd.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ht)
  rw [v12_joint_fderiv_spatial_slice _ t x w hdif]
  have he : (fun y => fderiv ℝ f (t,y) (0,v)) =
      (fun y => fderiv ℝ (fun z => f (t,z)) y v) :=
    funext (fun y => v12_joint_fderiv_spatial_slice f t y v (hdiff y))
  rw [he]

#print axioms v12_joint_fderiv_spatial_slice
#print axioms v12_joint_fderiv_time_slice
#print axioms v12_joint_second_spatial_slice
end SMScattering.W20Full
