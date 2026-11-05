import EulerNonuniqueness.General.TrilinearDiagonalDifference

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace
  cubicCoefficientThirdGroup cubicCoefficientThirdSpace

theorem norm_relative_cubic_error_le
    (initialOuter finalOuter : Space →L[ℝ] Space)
    (initialCubic finalCubic : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space)
    (initialRemainder finalRemainder first second : Space)
    {constant bound distance : ℝ}
    (constantNonnegative : 0 ≤ constant) (boundNonnegative : 0 ≤ bound) (distanceNonnegative : 0 ≤ distance)
    (outerNorm : ‖initialOuter‖ ≤ bound)
    (outerDifference : ‖initialOuter - finalOuter‖ ≤ bound * distance)
    (cubicNorm : ‖initialCubic‖ ≤ bound)
    (cubicDifference : ‖initialCubic - finalCubic‖ ≤ bound * distance)
    (remainderDifference : ‖initialRemainder - finalRemainder‖ ≤ constant *
      ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ + (‖first‖ + ‖second‖) ^ 3 * distance))
    (remainderNorm : ‖finalRemainder‖ ≤ constant * ‖second‖ ^ 3) :
    ‖(initialOuter initialRemainder - initialCubic first first first) -
      (finalOuter finalRemainder - finalCubic second second second)‖ ≤
      (2 * bound * constant + bound) *
        ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ + (‖first‖ + ‖second‖) ^ 3 * distance) := by
  let variation := (‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
    (‖first‖ + ‖second‖) ^ 3 * distance
  have variationNonnegative : 0 ≤ variation := by dsimp only [variation]; positivity
  have cubeBound : ‖second‖ ^ 3 ≤ (‖first‖ + ‖second‖) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) _
  have distanceCube : distance * ‖second‖ ^ 3 ≤ variation := by
    calc
      _ ≤ distance * (‖first‖ + ‖second‖) ^ 3 := mul_le_mul_of_nonneg_left cubeBound distanceNonnegative
      _ ≤ variation := by dsimp only [variation]; nlinarith [sq_nonneg (‖first‖ + ‖second‖), norm_nonneg (first - second)]
  have outerIdentity : initialOuter initialRemainder - finalOuter finalRemainder =
      initialOuter (initialRemainder - finalRemainder) + (initialOuter - finalOuter) finalRemainder := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have outerEstimate : ‖initialOuter initialRemainder - finalOuter finalRemainder‖ ≤
      (2 * bound * constant) * variation := by
    rw [outerIdentity]
    calc
      _ ≤ ‖initialOuter‖ * ‖initialRemainder - finalRemainder‖ +
          ‖initialOuter - finalOuter‖ * ‖finalRemainder‖ :=
        (norm_add_le _ _).trans (add_le_add (initialOuter.le_opNorm _)
          ((initialOuter - finalOuter).le_opNorm _))
      _ ≤ bound * (constant * variation) + (bound * distance) * (constant * ‖second‖ ^ 3) :=
        add_le_add (mul_le_mul outerNorm remainderDifference (norm_nonneg _) boundNonnegative)
          (mul_le_mul outerDifference remainderNorm (norm_nonneg _) (by positivity))
      _ = bound * constant * variation + (bound * constant) * (distance * ‖second‖ ^ 3) := by ring
      _ ≤ bound * constant * variation + (bound * constant) * variation :=
        add_le_add_left (mul_le_mul_of_nonneg_left distanceCube (by positivity)) _
      _ = _ := by ring
  have cubicEstimate : ‖initialCubic first first first - finalCubic second second second‖ ≤ bound * variation := by
    calc
      _ ≤ ‖initialCubic‖ * (‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
          ‖initialCubic - finalCubic‖ * ‖second‖ ^ 3 := norm_trilinear_diagonal_difference_le _ _ _ _
      _ ≤ bound * (‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
          (bound * distance) * ‖second‖ ^ 3 := by gcongr
      _ ≤ bound * variation := by
        dsimp only [variation]
        nlinarith [mul_le_mul_of_nonneg_left cubeBound (mul_nonneg boundNonnegative distanceNonnegative)]
  have identity : (initialOuter initialRemainder - initialCubic first first first) -
      (finalOuter finalRemainder - finalCubic second second second) =
      (initialOuter initialRemainder - finalOuter finalRemainder) -
        (initialCubic first first first - finalCubic second second second) := by abel
  rw [identity]
  exact (norm_sub_le _ _).trans ((add_le_add outerEstimate cubicEstimate).trans_eq (by ring))

end

end EulerNonuniqueness.General
