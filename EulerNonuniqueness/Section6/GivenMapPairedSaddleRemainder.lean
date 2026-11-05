import EulerNonuniqueness.Section6.GivenMapNormalFormPairedQuadratic
import EulerNonuniqueness.Section6.NormalFormErrorLinearBound
import EulerNonuniqueness.Section6.DilationFrequencySaddleError

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem givenMap_paired_saddle_remainder_bound
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∀ frequency firstDilation secondDilation : ℝ, ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      (1 / 2 : ℝ) ≤ firstDilation → (1 / 2 : ℝ) ≤ secondDilation →
      let firstChart := localNormalFormChart graph coordinate first
      let secondChart := localNormalFormChart graph coordinate second
      let difference := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
      let referenceSize := |secondChart.1| + |secondChart.2|
      ‖dilationFrequencySaddleError frequency firstDilation secondDilation firstChart secondChart +
          (frequency / firstDilation) •
            (localNormalFormError 1 graph coordinate first - localNormalFormError 1 graph coordinate second) +
          (frequency / firstDilation - frequency / secondDilation) • localNormalFormError 1 graph coordinate second‖ ≤
        constant * |frequency| *
          ((difference + referenceSize + |firstDilation - 1|) * difference +
            |firstDilation - secondDilation| * referenceSize) := by
  obtain ⟨quadraticRadius, quadraticPositive, quadraticConstant, quadraticOne, quadratic⟩ :=
    givenMap_localNormalFormError_paired_quadratic_bound graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨linearRadius, linearPositive, linearConstant, linearOne, linear⟩ :=
    localNormalFormError_exists_uniform_linear_chart_bound graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let constant := 16 + 2 * quadraticConstant + 4 * linearConstant
  have quadraticNonnegative : 0 ≤ quadraticConstant := zero_le_one.trans quadraticOne
  have linearNonnegative : 0 ≤ linearConstant := zero_le_one.trans linearOne
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith only [quadraticOne, linearOne]
  refine ⟨min quadraticRadius linearRadius, lt_min quadraticPositive linearPositive, constant, constantOne, ?_⟩
  intro frequency firstDilation secondDilation first second firstSmall secondSmall firstLower secondLower
  dsimp only
  let firstChart := localNormalFormChart graph coordinate first
  let secondChart := localNormalFormChart graph coordinate second
  let difference := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
  let referenceSize := |secondChart.1| + |secondChart.2|
  have differenceNonnegative : 0 ≤ difference := by dsimp only [difference]; positivity
  have referenceNonnegative : 0 ≤ referenceSize := by dsimp only [referenceSize]; positivity
  have pairBound : ‖localNormalFormError 1 graph coordinate first - localNormalFormError 1 graph coordinate second‖ ≤
      quadraticConstant * difference * (difference + referenceSize) :=
    quadratic first second (firstSmall.trans_le (min_le_left _ _)) (secondSmall.trans_le (min_le_left _ _))
  have referenceBound : ‖localNormalFormError 1 graph coordinate second‖ ≤ linearConstant * referenceSize :=
    linear second (secondSmall.trans_le (min_le_right _ _))
  have firstPositive : 0 < firstDilation := by linarith only [firstLower]
  have frequencyBound : |frequency / firstDilation| ≤ 2 * |frequency| := by
    rw [abs_div, abs_of_pos firstPositive]
    apply (div_le_iff₀ firstPositive).mpr
    nlinarith only [mul_nonneg (abs_nonneg frequency) (sub_nonneg.mpr firstLower)]
  have pairTerm : ‖(frequency / firstDilation) •
      (localNormalFormError 1 graph coordinate first - localNormalFormError 1 graph coordinate second)‖ ≤
      2 * |frequency| * (quadraticConstant * difference * (difference + referenceSize)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul frequencyBound pairBound (norm_nonneg _) (by positivity)
  have referenceTerm : ‖(frequency / firstDilation - frequency / secondDilation) •
      localNormalFormError 1 graph coordinate second‖ ≤
      (4 * |frequency| * |firstDilation - secondDilation|) * (linearConstant * referenceSize) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (dilation_frequency_difference_le frequency firstDilation secondDilation firstLower secondLower)
      referenceBound (norm_nonneg _) (by positivity)
  have dilationTerm : ‖dilationFrequencySaddleError frequency firstDilation secondDilation firstChart secondChart‖ ≤
      8 * |frequency| * |firstDilation - 1| * difference +
        16 * |frequency| * |firstDilation - secondDilation| * referenceSize := by
    have original := dilationFrequencySaddleError_norm_le frequency firstDilation secondDilation firstChart secondChart firstLower secondLower
    have sqrtBound : 2 * Real.sqrt 2 ≤ (4 : ℝ) := by
      have lower := Real.sqrt_nonneg (2 : ℝ)
      have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith only [lower, square]
    apply original.trans
    convert mul_le_mul_of_nonneg_right sqrtBound
      (show 0 ≤ 2 * |frequency| * |firstDilation - 1| * difference +
        4 * |frequency| * |firstDilation - secondDilation| * referenceSize by positivity) using 1
    ring
  have firstCoefficient : 8 ≤ constant := by dsimp only [constant]; linarith only [quadraticNonnegative, linearNonnegative]
  have quadraticCoefficient : 2 * quadraticConstant ≤ constant := by dsimp only [constant]; linarith only [linearNonnegative]
  have referenceCoefficient : 16 + 4 * linearConstant ≤ constant := by dsimp only [constant]; linarith only [quadraticNonnegative]
  calc
    _ ≤ ‖dilationFrequencySaddleError frequency firstDilation secondDilation firstChart secondChart‖ +
        ‖(frequency / firstDilation) •
          (localNormalFormError 1 graph coordinate first - localNormalFormError 1 graph coordinate second)‖ +
        ‖(frequency / firstDilation - frequency / secondDilation) • localNormalFormError 1 graph coordinate second‖ := norm_add₃_le
    _ ≤ (8 * |frequency| * |firstDilation - 1| * difference +
          16 * |frequency| * |firstDilation - secondDilation| * referenceSize) +
        2 * |frequency| * (quadraticConstant * difference * (difference + referenceSize)) +
        (4 * |frequency| * |firstDilation - secondDilation|) * (linearConstant * referenceSize) :=
      add_le_add (add_le_add dilationTerm pairTerm) referenceTerm
    _ = |frequency| * (8 * (|firstDilation - 1| * difference) +
        (2 * quadraticConstant) * (difference * (difference + referenceSize)) +
        (16 + 4 * linearConstant) * (|firstDilation - secondDilation| * referenceSize)) := by ring
    _ ≤ |frequency| * (constant * (|firstDilation - 1| * difference) +
        constant * (difference * (difference + referenceSize)) +
        constant * (|firstDilation - secondDilation| * referenceSize)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right firstCoefficient (by positivity))
          (mul_le_mul_of_nonneg_right quadraticCoefficient (by positivity)))
          (mul_le_mul_of_nonneg_right referenceCoefficient (by positivity))) (abs_nonneg frequency)
    _ = _ := by dsimp only [difference, referenceSize, firstChart, secondChart]; ring

end EulerNonuniqueness.Section6

