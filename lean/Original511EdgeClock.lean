import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory

namespace SM.K.Original511

private theorem clock_pointwise
    (e eStar J Cz A B c Ne T Ce R : ℝ)
    (he : 0 < e) (heStar : e ≤ eStar) (hJ : 0 < J)
    (hCz : 0 ≤ Cz) (hA : 0 ≤ A) (hB : 0 < B) (hc : 0 < c)
    (hNe : 0 ≤ Ne) (hT : 0 < T) (hTcap : T ≤ B ^ 2 * Ne ^ 2)
    (hCe : c * Ne ^ 2 ≤ Ce)
    (hLocal : |R| ≤ (4 * Real.sqrt 2 * A * Cz / J) *
      e ^ ((5:ℝ)/2) * Ne * Real.sqrt T) :
    |R| ≤ (4 * (Real.sqrt 2 * A * B * Cz *
      eStar ^ ((5:ℝ)/2) / (c*J))) * Ce := by
  have hBNe : 0 ≤ B * Ne := mul_nonneg (le_of_lt hB) hNe
  have hSqrtT : Real.sqrt T ≤ B * Ne := by
    have hAux : (Real.sqrt T)^2 ≤ (B * Ne)^2 := by
      rw [Real.sq_sqrt (le_of_lt hT)]
      nlinarith [hTcap]
    nlinarith [Real.sqrt_nonneg T]
  have hPow : e ^ ((5:ℝ)/2) ≤ eStar ^ ((5:ℝ)/2) := by
    exact Real.rpow_le_rpow (le_of_lt he) heStar (by norm_num)
  have hCoef : 0 ≤ 4 * Real.sqrt 2 * A * Cz / J := by positivity
  have hPowerNonneg : 0 ≤ eStar ^ ((5:ℝ)/2) := Real.rpow_nonneg (le_trans (le_of_lt he) heStar) _
  have hCoeff : 0 ≤ 4 * (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J)) := by positivity
  calc
    |R| ≤ (4 * Real.sqrt 2 * A * Cz / J) * e ^ ((5:ℝ)/2) * Ne * Real.sqrt T := hLocal
    _ ≤ (4 * Real.sqrt 2 * A * Cz / J) * eStar ^ ((5:ℝ)/2) * Ne * (B * Ne) := by
      gcongr
    _ = (4 * (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J))) * (c * Ne ^ 2) := by
      field_simp
      ring
    _ ≤ (4 * (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J))) * Ce := by
      gcongr

/-- The original time-weight `χ(e)Nₑ²/(eTₑ)`. -/
private def edgeWeight (chi : ℝ → ℝ) (Ne Te : ℝ → ℝ → ℝ)
    (e t : ℝ) : ℝ := chi e * Ne e t ^ 2 / (e * Te e t)

private theorem edgeWeight_nonneg
    (chi : ℝ → ℝ) (Ne Te : ℝ → ℝ → ℝ)
    (e t : ℝ) (hchi : 0 ≤ chi e) (he : 0 < e) (hT : 0 < Te e t) :
    0 ≤ edgeWeight chi Ne Te e t := by
  unfold edgeWeight
  positivity

/-- Original Lemma 5.11's clock transfer under its original heat-layer
hypotheses and the local tracefree edge estimate. This part is conditional on
`hLocal`, which must be discharged by the local statement to count 5.11. -/
theorem edge_clock_integral
    (I : Set ℝ) (chi : ℝ → ℝ) (Ne Te Ce Redge : ℝ → ℝ → ℝ)
    (eStar J Cz A B c : ℝ)
    (hJ : 0 < J) (hCz : 0 ≤ Cz) (hA : 0 ≤ A)
    (hB : 0 < B) (hc : 0 < c)
    (hchi : ∀ e, 0 ≤ chi e)
    (hchiOne : (∫ e, chi e) = 1)
    (hsupp : ∀ e, chi e ≠ 0 → 0 < e ∧ e ≤ eStar)
    (hNe : ∀ e t, chi e ≠ 0 → 0 ≤ Ne e t)
    (hTe : ∀ e t, chi e ≠ 0 → 0 < Te e t)
    (hTcap : ∀ e t, chi e ≠ 0 → Te e t ≤ B ^ 2 * Ne e t ^ 2)
    (hCe : ∀ e t, chi e ≠ 0 → c * Ne e t ^ 2 ≤ Ce e t)
    (hLocal : ∀ e t, chi e ≠ 0 →
      |Redge e t| ≤ (4 * Real.sqrt 2 * A * Cz / J) *
        e ^ ((5:ℝ)/2) * Ne e t * Real.sqrt (Te e t))
    (hEdgeInnerInt : ∀ t, Integrable
      (fun e => edgeWeight chi Ne Te e t * Redge e t))
    (hCInnerInt : ∀ t, Integrable
      (fun e => edgeWeight chi Ne Te e t * Ce e t))
    (hEdgeOuterInt : Integrable
      (fun t => ∫ e, edgeWeight chi Ne Te e t * Redge e t)
      ((volume : Measure ℝ).restrict I))
    (hCOuterInt : Integrable
      (fun t => ∫ e, edgeWeight chi Ne Te e t * Ce e t)
      ((volume : Measure ℝ).restrict I)) :
    |∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Redge e t)| ≤
      (Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c*J)) *
        (4 * (∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Ce e t))) := by
  let coeff : ℝ := Real.sqrt 2 * A * B * Cz * eStar ^ ((5:ℝ)/2) / (c * J)
  have hCoeffNonneg : 0 ≤ 4 * coeff := by
    have heStarNonneg : 0 ≤ eStar := by
      have hSome : ∃ e, chi e ≠ 0 := by
        by_contra hn
        have heq : chi = (fun _ => (0:ℝ)) := by
          funext e
          by_contra hx
          exact hn ⟨e, hx⟩
        simp [heq] at hchiOne
      obtain ⟨e, he⟩ := hSome
      exact le_trans (le_of_lt (hsupp e he).1) (hsupp e he).2
    dsimp [coeff]
    positivity
  have hPointwise (e t : ℝ) :
      |edgeWeight chi Ne Te e t * Redge e t| ≤
        (4 * coeff) * (edgeWeight chi Ne Te e t * Ce e t) := by
    by_cases hz : chi e = 0
    · simp [edgeWeight, hz]
    have he : 0 < e := (hsupp e hz).1
    have ht : 0 < Te e t := hTe e t hz
    have hw : 0 ≤ edgeWeight chi Ne Te e t :=
      edgeWeight_nonneg chi Ne Te e t (hchi e) he ht
    have hpt := clock_pointwise e eStar J Cz A B c (Ne e t) (Te e t)
      (Ce e t) (Redge e t) he (hsupp e hz).2 hJ hCz hA hB hc
      (hNe e t hz) ht (hTcap e t hz) (hCe e t hz) (hLocal e t hz)
    calc
      |edgeWeight chi Ne Te e t * Redge e t| =
          edgeWeight chi Ne Te e t * |Redge e t| := by
            rw [abs_mul, abs_of_nonneg hw]
      _ ≤ edgeWeight chi Ne Te e t * ((4 * coeff) * Ce e t) := by
        gcongr
      _ = (4 * coeff) * (edgeWeight chi Ne Te e t * Ce e t) := by ring
  have hI (t : ℝ) :
      |∫ e, edgeWeight chi Ne Te e t * Redge e t| ≤
        (4 * coeff) * (∫ e, edgeWeight chi Ne Te e t * Ce e t) := by
    calc
      |∫ e, edgeWeight chi Ne Te e t * Redge e t| =
          ‖∫ e, edgeWeight chi Ne Te e t * Redge e t‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ e, ‖edgeWeight chi Ne Te e t * Redge e t‖ := norm_integral_le_integral_norm _
      _ = ∫ e, |edgeWeight chi Ne Te e t * Redge e t| := by simp only [Real.norm_eq_abs]
      _ ≤ ∫ e, (4 * coeff) * (edgeWeight chi Ne Te e t * Ce e t) := by
        exact integral_mono (hEdgeInnerInt t).abs ((hCInnerInt t).const_mul _) (fun e => hPointwise e t)
      _ = (4 * coeff) * (∫ e, edgeWeight chi Ne Te e t * Ce e t) := integral_const_mul _ _
  calc
    |∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Redge e t)| =
        ‖∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Redge e t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in I, ‖∫ e, edgeWeight chi Ne Te e t * Redge e t‖ := norm_integral_le_integral_norm _
    _ = ∫ t in I, |∫ e, edgeWeight chi Ne Te e t * Redge e t| := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ t in I, (4 * coeff) * (∫ e, edgeWeight chi Ne Te e t * Ce e t) := by
      exact integral_mono hEdgeOuterInt.abs (hCOuterInt.const_mul _) hI
    _ = coeff * (4 * (∫ t in I, (∫ e, edgeWeight chi Ne Te e t * Ce e t))) := by
      rw [integral_const_mul]
      ring

#print axioms SM.K.Original511.edge_clock_integral

/-- Sharp bridge from the actual local L² tracefree estimate to the
heat-layer estimate assumed by edge_clock_integral.
No hLocal is taken as input: it is DERIVED with the mass 2e and the
D W thermal norm bound. -/
theorem local_to_heat_layer
    (e J Cz A Ne Te M D Redge : ℝ)
    (he : 0 < e) (hJ : 0 < J) (hCz : 0 ≤ Cz)
    (hA : 0 ≤ A) (hN : 0 ≤ Ne) (hTe : 0 < Te)
    (hMass : M = 2 * e)
    (hD : Real.sqrt D ≤ A * e * Ne * Real.sqrt Te)
    (hLocal : |Redge| ≤
        4 * (Cz / (2 * J)) * M * Real.sqrt M * Real.sqrt D) :
    |Redge| ≤ (4 * Real.sqrt 2 * A * Cz / J) *
      e ^ ((5:ℝ)/2) * Ne * Real.sqrt Te := by
  have hp : e ^ ((5:ℝ)/2) = e ^ 2 * Real.sqrt e := by
    calc
      e ^ ((5:ℝ)/2) = e ^ ((2:ℝ) + (1:ℝ)/2) := by congr 1; ring
      _ = e ^ (2:ℝ) * e ^ ((1:ℝ)/2) := Real.rpow_add he _ _
      _ = e ^ 2 * Real.sqrt e := by
        rw [← Real.sqrt_eq_rpow]
  have hr : Real.sqrt (2 * e) = Real.sqrt 2 * Real.sqrt e := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hcoef : 0 ≤ 4 * (Cz / (2 * J)) *
      (2 * e) * Real.sqrt (2 * e) := by positivity
  calc
    |Redge| ≤
        4 * (Cz / (2 * J)) * M * Real.sqrt M * Real.sqrt D := hLocal
    _ = 4 * (Cz / (2 * J)) * (2 * e) *
        Real.sqrt (2 * e) * Real.sqrt D := by rw [hMass]
    _ ≤ 4 * (Cz / (2 * J)) * (2 * e) *
        Real.sqrt (2 * e) * (A * e * Ne * Real.sqrt Te) :=
      mul_le_mul_of_nonneg_left hD hcoef
    _ = (4 * Real.sqrt 2 * A * Cz / J) *
          e ^ ((5:ℝ)/2) * Ne * Real.sqrt Te := by
      rw [hr, hp]
      field_simp
      ring

#print axioms SM.K.Original511.local_to_heat_layer

end SM.K.Original511