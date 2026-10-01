import lean.v12.V12_YWUCanonicalSliceDerivatives
import lean.v12.V12_SourceProducts

/-! Derive the actual canonical scalar PDE from the original two-component
curried equation. Projection, time derivatives, spatial derivatives and
second derivatives are all proved compatible with the same original field. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace SMScattering.W20Full

theorem v12_component_contDiffOn
    (a b : ℝ) (f : V12Spacetime → V12Field) (j : Fin 2)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f z j)
      (Prod.fst ⁻¹' Set.Ioo a b) := by
  let P := (EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ
  exact P.contDiff.comp_contDiffOn hf

theorem v12_component_fderiv
    (f : V12Spacetime → V12Field) (z v : V12Spacetime) (j : Fin 2)
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun x => f x j) z v = (fderiv ℝ f z v) j := by
  let P := (EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ
  have h := P.hasFDerivAt.comp z hf.hasFDerivAt
  have he := congrArg (fun L : V12Spacetime →L[ℝ] ℂ => L v) h.fderiv
  exact he

theorem v12_component_second_fderiv
    (a b : ℝ) (f : V12Spacetime → V12Field)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (z v w : V12Spacetime) (hz : z ∈ Prod.fst ⁻¹' Set.Ioo a b) (j : Fin 2) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => f y j) x v) z w =
      (fderiv ℝ (fun x => fderiv ℝ f x v) z w) j := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hdiff (x : V12Spacetime) (hx : x ∈ U) : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have he : Set.EqOn (fun x => fderiv ℝ (fun y => f y j) x v)
      (fun x => (fderiv ℝ f x v) j) U :=
    fun x hx => v12_component_fderiv f x v j (hdiff x hx)
  have hd := (hf.fderiv_of_isOpen hU (by simp)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : V12Spacetime => v) U)
  have hdf : DifferentiableAt ℝ (fun x => fderiv ℝ f x v) z :=
    (hd.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  rw [v12_open_eqOn_fderiv U hU _ _ he hz]
  exact v12_component_fderiv _ z w j hdf

theorem v12_original_curried_scalar_PDE
    (a b : ℝ) (q dq : ℝ → V12Spatial → V12Field)
    (A : Fin 2 → V12Spacetime → ℂ) (V W : V12Spacetime → ℂ)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry q) (Prod.fst ⁻¹' Set.Ioo a b))
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : V12Spatial)
    (hd : HasDerivAt (fun s => q s x) (dq t x) t)
    (hPDE : let e := EuclideanSpace.basisFun (Fin 2) ℝ
      Complex.I • dq t x +
        (fderiv ℝ (fun y => fderiv ℝ (q t) y (e 0)) x (e 0) +
         fderiv ℝ (fun y => fderiv ℝ (q t) y (e 1)) x (e 1)) =
      (2 * Complex.I) •
        (A 0 (t,x) • fderiv ℝ (q t) x (e 0) + A 1 (t,x) • fderiv ℝ (q t) x (e 1)) +
      v12_zeroOrderProduct V W (Function.uncurry q) (t,x)) (j : Fin 2) :
    Complex.I * fderiv ℝ (fun z => q z.1 z.2 j) (t,x) v12_timeDirection +
      (fderiv ℝ (fun z => fderiv ℝ (fun y => q y.1 y.2 j) z (v12_spatialDirection 0))
          (t,x) (v12_spatialDirection 0) +
       fderiv ℝ (fun z => fderiv ℝ (fun y => q y.1 y.2 j) z (v12_spatialDirection 1))
          (t,x) (v12_spatialDirection 1)) =
    (2 * Complex.I) *
      (A 0 (t,x) * fderiv ℝ (fun z => q z.1 z.2 j) (t,x) (v12_spatialDirection 0) +
       A 1 (t,x) * fderiv ℝ (fun z => q z.1 z.2 j) (t,x) (v12_spatialDirection 1)) +
      (V (t,x) * q t x j + W (t,x) * star (q t x j)) := by
  let f : V12Spacetime → V12Field := fun z => q z.1 z.2
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hU : IsOpen (Prod.fst ⁻¹' Set.Ioo a b : Set V12Spacetime) :=
    isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hf : DifferentiableAt ℝ f (t,x) :=
    (hs.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ht)
  have htime := v12_joint_fderiv_time_slice f t x (dq t x) hf hd
  have hspace (k : Fin 2) := v12_joint_fderiv_spatial_slice f t x (e k) hf
  have hsecond (k : Fin 2) := v12_joint_second_spatial_slice a b f hs t ht x (e k) (e k)
  dsimp only [v12_spatialDirection]
  rw [v12_component_fderiv f (t,x) v12_timeDirection j hf, htime]
  rw [v12_component_second_fderiv a b f hs (t,x) (0,e 0)
    (0,e 0) ht j,
    v12_component_second_fderiv a b f hs (t,x) (0,e 1)
    (0,e 1) ht j]
  change Complex.I * dq t x j +
    ((fderiv ℝ (fun z => fderiv ℝ f z (0,e 0)) (t,x) (0,e 0)) j +
     (fderiv ℝ (fun z => fderiv ℝ f z (0,e 1)) (t,x) (0,e 1)) j) = _
  rw [hsecond 0, hsecond 1,
    v12_component_fderiv f (t,x) (0,e 0) j hf,
    v12_component_fderiv f (t,x) (0,e 1) j hf,
    hspace 0, hspace 1]
  have he := congrArg (fun u : V12Field => u j) hPDE
  simpa only [f, e, Function.uncurry, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v12_zeroOrderProduct,
    v12_conjugateField_apply] using he

#print axioms v12_component_fderiv
#print axioms v12_component_second_fderiv
#print axioms v12_original_curried_scalar_PDE
end SMScattering.W20Full
