import Mathlib

namespace EulerNonuniqueness.General

theorem abs_mean_difference_of_relative_constraint
    {initialCoefficient finalCoefficient initialMean finalMean initialError finalError : ℝ}
    {lower constant sumSize transverseDifference parameterDifference finalSize radialNorm : ℝ}
    (lowerPositive : 0 < lower) (constantNonnegative : 0 ≤ constant)
    (sizeNonnegative : 0 ≤ sumSize) (transverseNonnegative : 0 ≤ transverseDifference)
    (parameterNonnegative : 0 ≤ parameterDifference) (finalNonnegative : 0 ≤ finalSize)
    (radialNonnegative : 0 ≤ radialNorm)
    (coefficientLower : lower ≤ initialCoefficient)
    (coefficientDifference : |initialCoefficient - finalCoefficient| ≤ constant * parameterDifference)
    (initialConstraint : initialCoefficient * initialMean + initialError = 0)
    (finalConstraint : finalCoefficient * finalMean + finalError = 0)
    (finalMeanBound : |finalMean| ≤ constant * finalSize ^ 2)
    (errorDifference : |initialError - finalError| ≤ constant *
      (sumSize * (transverseDifference + radialNorm * |initialMean - finalMean|) +
        parameterDifference * finalSize ^ 2))
    (small : constant * sumSize * radialNorm ≤ lower / 2) :
    |initialMean - finalMean| ≤ (2 / lower) *
      (constant * sumSize * transverseDifference +
        (constant ^ 2 + constant) * parameterDifference * finalSize ^ 2) := by
  have coefficientPositive : 0 < initialCoefficient := lt_of_lt_of_le lowerPositive coefficientLower
  have identity : initialCoefficient * (initialMean - finalMean) =
      (finalCoefficient - initialCoefficient) * finalMean + (finalError - initialError) := by
    nlinarith [initialConstraint, finalConstraint]
  have mainBound : lower * |initialMean - finalMean| ≤
      constant ^ 2 * parameterDifference * finalSize ^ 2 + constant *
        (sumSize * (transverseDifference + radialNorm * |initialMean - finalMean|) +
          parameterDifference * finalSize ^ 2) := by
    calc
      _ ≤ initialCoefficient * |initialMean - finalMean| :=
        mul_le_mul_of_nonneg_right coefficientLower (abs_nonneg _)
      _ = |initialCoefficient * (initialMean - finalMean)| := by
        rw [abs_mul, abs_of_pos coefficientPositive]
      _ ≤ |finalCoefficient - initialCoefficient| * |finalMean| + |finalError - initialError| := by
        rw [identity]
        exact (abs_add _ _).trans_eq (by rw [abs_mul])
      _ ≤ (constant * parameterDifference) * (constant * finalSize ^ 2) + constant *
          (sumSize * (transverseDifference + radialNorm * |initialMean - finalMean|) +
            parameterDifference * finalSize ^ 2) :=
        add_le_add (mul_le_mul (by simpa only [abs_sub_comm] using coefficientDifference)
          finalMeanBound (abs_nonneg _) (by positivity))
          (by simpa only [abs_sub_comm] using errorDifference)
      _ = _ := by ring
  have absorbed : (lower / 2) * |initialMean - finalMean| ≤
      constant * sumSize * transverseDifference +
        (constant ^ 2 + constant) * parameterDifference * finalSize ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right small (abs_nonneg (initialMean - finalMean))]
  have actual := (le_div_iff₀ (half_pos lowerPositive)).2 (by simpa only [mul_comm] using absorbed)
  convert actual using 1 <;> field_simp <;> ring

end EulerNonuniqueness.General
