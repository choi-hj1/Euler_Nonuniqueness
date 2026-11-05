import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem graded_stable_integral_absorption
    {dilation stable shape forcing : ℝ → ℝ}
    {horizon omega constant referenceSize shapeCap rate : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (omegaPositive : 0 < omega)
    (constantNonnegative : 0 ≤ constant) (referenceNonnegative : 0 ≤ referenceSize)
    (shapeCapNonnegative : 0 ≤ shapeCap)
    (constantShapeSmall : constant * shapeCap ≤ 1 / 4)
    (constantReferenceSmall : constant * referenceSize ≤ 1 / 4)
    (dilationContinuous : ContinuousOn dilation (Icc 0 horizon))
    (stableContinuous : ContinuousOn stable (Icc 0 horizon))
    (shapeContinuous : ContinuousOn shape (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (dilationNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ dilation time)
    (stableNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ stable time)
    (shapeNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ shape time)
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (shapeBound : ∀ time ∈ Icc 0 horizon, shape time ≤ shapeCap)
    (rateBound : 2 * omega ≤ rate)
    (stableBound : rate * (∫ time in (0 : ℝ)..horizon, stable time) ≤
      (∫ time in (0 : ℝ)..horizon, forcing time) + constant * omega *
        ∫ time in (0 : ℝ)..horizon,
          (referenceSize + dilation time + stable time) * shape time + referenceSize * dilation time) :
    omega * (∫ time in (0 : ℝ)..horizon, referenceSize + dilation time + stable time) ≤
      2 * omega * referenceSize * horizon +
        2 * omega * (∫ time in (0 : ℝ)..horizon, dilation time) +
        ∫ time in (0 : ℝ)..horizon, forcing time := by
  let coefficient := fun time => referenceSize + dilation time + stable time
  let graded := fun time => coefficient time * shape time + referenceSize * dilation time
  have coefficientContinuous : ContinuousOn coefficient (Icc 0 horizon) :=
    (continuousOn_const.add dilationContinuous).add stableContinuous
  have gradedContinuous : ContinuousOn graded (Icc 0 horizon) :=
    (coefficientContinuous.mul shapeContinuous).add (continuousOn_const.mul dilationContinuous)
  have upperContinuous : ContinuousOn
      (fun time => shapeCap * coefficient time + referenceSize * dilation time) (Icc 0 horizon) :=
    (continuousOn_const.mul coefficientContinuous).add (continuousOn_const.mul dilationContinuous)
  have dilationIntegrable := dilationContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have stableIntegrable := stableContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have forcingIntegrable := forcingContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have coefficientIntegrable := coefficientContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have gradedIntegrable := gradedContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have upperIntegrable := upperContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have coefficientNonnegative (time : ℝ) (inside : time ∈ Icc 0 horizon) : 0 ≤ coefficient time :=
    add_nonneg (add_nonneg referenceNonnegative (dilationNonnegative time inside)) (stableNonnegative time inside)
  have gradedNonnegative (time : ℝ) (inside : time ∈ Icc 0 horizon) : 0 ≤ graded time :=
    add_nonneg (mul_nonneg (coefficientNonnegative time inside) (shapeNonnegative time inside))
      (mul_nonneg referenceNonnegative (dilationNonnegative time inside))
  have upperNonnegative (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      0 ≤ shapeCap * coefficient time + referenceSize * dilation time :=
    add_nonneg (mul_nonneg shapeCapNonnegative (coefficientNonnegative time inside))
      (mul_nonneg referenceNonnegative (dilationNonnegative time inside))
  have gradedComparison := intervalIntegral.integral_mono_on horizonNonnegative gradedIntegrable upperIntegrable (by
    intro time inside
    have point := mul_le_mul_of_nonneg_left (shapeBound time inside) (coefficientNonnegative time inside)
    exact add_le_add_right (point.trans_eq (mul_comm _ _)) _)
  rw [intervalIntegral.integral_add (coefficientIntegrable.const_mul shapeCap) (dilationIntegrable.const_mul referenceSize),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at gradedComparison
  have coefficientIntegral : (∫ time in (0 : ℝ)..horizon, coefficient time) =
      referenceSize * horizon + (∫ time in (0 : ℝ)..horizon, dilation time) +
        ∫ time in (0 : ℝ)..horizon, stable time := by
    dsimp only [coefficient]
    rw [intervalIntegral.integral_add (intervalIntegrable_const.add dilationIntegrable) stableIntegrable,
      intervalIntegral.integral_add intervalIntegrable_const dilationIntegrable, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have stableIntegralNonnegative : 0 ≤ ∫ time in (0 : ℝ)..horizon, stable time :=
    intervalIntegral.integral_nonneg horizonNonnegative stableNonnegative
  have dilationIntegralNonnegative : 0 ≤ ∫ time in (0 : ℝ)..horizon, dilation time :=
    intervalIntegral.integral_nonneg horizonNonnegative dilationNonnegative
  have forcingIntegralNonnegative : 0 ≤ ∫ time in (0 : ℝ)..horizon, forcing time :=
    intervalIntegral.integral_nonneg horizonNonnegative forcingNonnegative
  have combined := (mul_le_mul_of_nonneg_right rateBound stableIntegralNonnegative).trans
    (stableBound.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left gradedComparison (mul_nonneg constantNonnegative omegaPositive.le))
      (∫ time in (0 : ℝ)..horizon, forcing time)))
  rw [coefficientIntegral] at combined
  let referenceCost := omega * referenceSize * horizon
  let dilationCost := omega * ∫ time in (0 : ℝ)..horizon, dilation time
  let stableCost := omega * ∫ time in (0 : ℝ)..horizon, stable time
  let forcingCost := ∫ time in (0 : ℝ)..horizon, forcing time
  have referenceCostNonnegative : 0 ≤ referenceCost :=
    mul_nonneg (mul_nonneg omegaPositive.le referenceNonnegative) horizonNonnegative
  have dilationCostNonnegative : 0 ≤ dilationCost := mul_nonneg omegaPositive.le dilationIntegralNonnegative
  have stableCostNonnegative : 0 ≤ stableCost := mul_nonneg omegaPositive.le stableIntegralNonnegative
  have forcingCostNonnegative : 0 ≤ forcingCost := forcingIntegralNonnegative
  have scalar : 2 * stableCost ≤ forcingCost + constant * shapeCap *
      (referenceCost + dilationCost + stableCost) + constant * referenceSize * dilationCost := by
    convert combined using 1 <;> dsimp only [referenceCost, dilationCost, stableCost, forcingCost] <;> ring
  have shapeAbsorption := mul_le_mul_of_nonneg_right constantShapeSmall
    (add_nonneg (add_nonneg referenceCostNonnegative dilationCostNonnegative) stableCostNonnegative)
  have referenceAbsorption := mul_le_mul_of_nonneg_right constantReferenceSmall dilationCostNonnegative
  have absorbed : referenceCost + dilationCost + stableCost ≤
      2 * referenceCost + 2 * dilationCost + forcingCost := by
    linarith only [scalar, shapeAbsorption, referenceAbsorption, referenceCostNonnegative,
      dilationCostNonnegative, forcingCostNonnegative]
  change omega * (∫ time in (0 : ℝ)..horizon, coefficient time) ≤ _
  rw [coefficientIntegral]
  convert absorbed using 1 <;> dsimp only [referenceCost, dilationCost, stableCost, forcingCost] <;> ring

end EulerNonuniqueness.General
