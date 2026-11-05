import Mathlib

namespace EulerNonuniqueness.General

theorem paired_affine_remainder_scalar_budget
    {first second increment baseDifference amplitude sourceConstant derivativeConstant
      generatorConstant correctionConstant taylorConstant size : ℝ}
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (incrementNonnegative : 0 ≤ increment) (baseNonnegative : 0 ≤ baseDifference)
    (amplitudeNonnegative : 0 ≤ amplitude) (sourceNonnegative : 0 ≤ sourceConstant)
    (derivativeNonnegative : 0 ≤ derivativeConstant) (generatorNonnegative : 0 ≤ generatorConstant)
    (correctionNonnegative : 0 ≤ correctionConstant) (taylorNonnegative : 0 ≤ taylorConstant)
    (sizeBound : first + second ≤ size) :
    let budget := size * increment + baseDifference * size ^ 2
    sourceConstant * amplitude * budget +
      (derivativeConstant * first ^ 2 * (2 * amplitude * baseDifference) +
        derivativeConstant * budget * (6 * amplitude)) +
      (generatorConstant * first *
          (correctionConstant * amplitude * increment + correctionConstant * amplitude * baseDifference * second) +
        generatorConstant * (increment + baseDifference * second) * (correctionConstant * amplitude * second)) +
      (correctionConstant * amplitude * taylorConstant * budget +
        correctionConstant * amplitude * baseDifference * taylorConstant * second ^ 2) ≤
      amplitude * (sourceConstant + 8 * derivativeConstant + 2 * generatorConstant * correctionConstant +
        2 * correctionConstant * taylorConstant) * budget := by
  let budget := size * increment + baseDifference * size ^ 2
  have sizeNonnegative : 0 ≤ size := (add_nonneg firstNonnegative secondNonnegative).trans sizeBound
  have firstBound : first ≤ size := by linarith
  have secondBound : second ≤ size := by linarith
  have firstSquare : first ^ 2 ≤ size ^ 2 := pow_le_pow_left₀ firstNonnegative firstBound 2
  have secondSquare : second ^ 2 ≤ size ^ 2 := pow_le_pow_left₀ secondNonnegative secondBound 2
  have firstCost : baseDifference * first ^ 2 ≤ budget := by
    exact (mul_le_mul_of_nonneg_left firstSquare baseNonnegative).trans
      (le_add_of_nonneg_left (mul_nonneg sizeNonnegative incrementNonnegative))
  have secondCost : baseDifference * second ^ 2 ≤ budget := by
    exact (mul_le_mul_of_nonneg_left secondSquare baseNonnegative).trans
      (le_add_of_nonneg_left (mul_nonneg sizeNonnegative incrementNonnegative))
  have mixedCost : first * increment + baseDifference * first * second + increment * second + baseDifference * second ^ 2 ≤ 2 * budget := by
    calc
      _ = (first + second) * increment + baseDifference * ((first + second) * second) := by ring
      _ ≤ size * increment + baseDifference * (size * size) := by gcongr
      _ ≤ 2 * budget := by dsimp [budget]; nlinarith [mul_nonneg sizeNonnegative incrementNonnegative]
  dsimp only
  change sourceConstant * amplitude * budget +
    (derivativeConstant * first ^ 2 * (2 * amplitude * baseDifference) + derivativeConstant * budget * (6 * amplitude)) +
    (generatorConstant * first * (correctionConstant * amplitude * increment + correctionConstant * amplitude * baseDifference * second) +
      generatorConstant * (increment + baseDifference * second) * (correctionConstant * amplitude * second)) +
    (correctionConstant * amplitude * taylorConstant * budget + correctionConstant * amplitude * baseDifference * taylorConstant * second ^ 2) ≤ _
  calc
    _ = amplitude * (sourceConstant * budget +
        (2 * derivativeConstant * (baseDifference * first ^ 2) + 6 * derivativeConstant * budget) +
        generatorConstant * correctionConstant * (first * increment + baseDifference * first * second + increment * second + baseDifference * second ^ 2) +
        correctionConstant * taylorConstant * (budget + baseDifference * second ^ 2)) := by ring
    _ ≤ amplitude * (sourceConstant * budget +
        (2 * derivativeConstant * budget + 6 * derivativeConstant * budget) +
        generatorConstant * correctionConstant * (2 * budget) +
        correctionConstant * taylorConstant * (budget + budget)) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
