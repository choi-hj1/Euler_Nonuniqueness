import EulerNonuniqueness.General.FiberPrimitive
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Module

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness

theorem fiberPrimitive_zero {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (coefficient : ℝ × ℝ → Value) (graph : ℝ → ℝ)
    (graphZero : graph 0 = 0) (coefficientZero : coefficient 0 = 0) :
    fiberPrimitive coefficient graph 0 = 0 := by
  simp only [fiberPrimitive, Prod.fst_zero, Prod.snd_zero, graphZero, mul_zero, add_zero,
    show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, coefficientZero, intervalIntegral.integral_zero]

theorem fiberPrimitive_lipschitz_between {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    {coefficient : ℝ × ℝ → Value} {graph : ℝ → ℝ} {region : Set (ℝ × ℝ)}
    {bound : ℝ≥0} {graphBound : ℝ} (first second : ℝ × ℝ)
    (coefficientLipschitz : LipschitzOnWith bound coefficient region)
    (graphNonnegative : 0 ≤ graphBound)
    (graphDifference : |graph first.1 - graph second.1| ≤ graphBound * |first.1 - second.1|)
    (firstInside : ∀ parameter ∈ Icc (0 : ℝ) 1, (first.1, graph first.1 + parameter * first.2) ∈ region)
    (secondInside : ∀ parameter ∈ Icc (0 : ℝ) 1, (second.1, graph second.1 + parameter * second.2) ∈ region) :
    ‖fiberPrimitive coefficient graph first - fiberPrimitive coefficient graph second‖ ≤
      (bound : ℝ) * ((1 + graphBound) * |first.1 - second.1| + |first.2 - second.2|) := by
  have interval : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le (by norm_num)
  have firstContinuous : ContinuousOn (fun parameter => coefficient (first.1, graph first.1 + parameter * first.2)) (uIcc 0 1) :=
    coefficientLipschitz.continuousOn.comp (by fun_prop)
      (fun parameter member => firstInside parameter (interval ▸ member))
  have secondContinuous : ContinuousOn (fun parameter => coefficient (second.1, graph second.1 + parameter * second.2)) (uIcc 0 1) :=
    coefficientLipschitz.continuousOn.comp (by fun_prop)
      (fun parameter member => secondInside parameter (interval ▸ member))
  have differenceBound (parameter : ℝ) (member : parameter ∈ Icc (0 : ℝ) 1) :
      ‖coefficient (first.1, graph first.1 + parameter * first.2) - coefficient (second.1, graph second.1 + parameter * second.2)‖ ≤
        (bound : ℝ) * ((1 + graphBound) * |first.1 - second.1| + |first.2 - second.2|) := by
    have actual := (lipschitzOnWith_iff_norm_sub_le.mp coefficientLipschitz)
      (firstInside parameter member) (secondInside parameter member)
    apply actual.trans
    apply mul_le_mul_of_nonneg_left _ bound.coe_nonneg
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    have secondIdentity : (graph first.1 + parameter * first.2) - (graph second.1 + parameter * second.2) =
        (graph first.1 - graph second.1) + parameter * (first.2 - second.2) := by ring
    have parameterBound : |parameter| ≤ 1 := by rw [abs_of_nonneg member.1]; exact member.2
    have stableBound := (abs_add (graph first.1 - graph second.1) (parameter * (first.2 - second.2))).trans
      (add_le_add graphDifference (by simpa only [abs_mul, one_mul] using mul_le_mul_of_nonneg_right parameterBound (abs_nonneg (first.2 - second.2))))
    rw [secondIdentity]
    apply max_le
    · nlinarith only [graphNonnegative, abs_nonneg (first.1 - second.1), abs_nonneg (first.2 - second.2)]
    · nlinarith only [stableBound, abs_nonneg (first.1 - second.1)]
  unfold fiberPrimitive
  rw [← intervalIntegral.integral_sub firstContinuous.intervalIntegrable secondContinuous.intervalIntegrable]
  have actual := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun parameter member => differenceBound parameter (by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at member
      exact ⟨member.1.le, member.2⟩))
  simpa only [sub_zero, abs_one, mul_one] using actual

theorem graded_fiber_product_difference {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {firstFactor secondFactor : Value} {firstUnstable secondUnstable firstStable secondStable constant : ℝ}
    (constantNonnegative : 0 ≤ constant)
    (firstBound : ‖firstFactor‖ ≤ constant * (|firstUnstable| + |firstStable|))
    (differenceBound : ‖firstFactor - secondFactor‖ ≤ constant * (|firstUnstable - secondUnstable| + |firstStable - secondStable|)) :
    ‖firstStable • firstFactor - secondStable • secondFactor‖ ≤
      constant * ((|firstStable| + |secondStable|) * |firstUnstable - secondUnstable| +
        (|firstUnstable| + |secondUnstable| + |firstStable| + |secondStable|) * |firstStable - secondStable|) := by
  have identity : firstStable • firstFactor - secondStable • secondFactor =
      (firstStable - secondStable) • firstFactor + secondStable • (firstFactor - secondFactor) := by module
  rw [identity]
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs]
  have actual := add_le_add (mul_le_mul_of_nonneg_left firstBound (abs_nonneg (firstStable - secondStable)))
    (mul_le_mul_of_nonneg_left differenceBound (abs_nonneg secondStable))
  apply actual.trans
  have firstExtra : 0 ≤ constant * |firstStable| * |firstUnstable - secondUnstable| := by positivity
  have secondExtra : 0 ≤ constant * |secondUnstable| * |firstStable - secondStable| := by positivity
  nlinarith only [firstExtra, secondExtra]

end EulerNonuniqueness
