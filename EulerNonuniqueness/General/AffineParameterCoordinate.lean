import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem affine_parameter_coordinate_difference
    (data firstBase secondBase firstPrimitive secondPrimitive : Space)
    (firstCorrection secondCorrection : Space →L[ℝ] Space) :
    (data - firstPrimitive - firstCorrection (data - firstBase)) -
        (data - secondPrimitive - secondCorrection (data - secondBase)) =
      -(firstPrimitive - secondPrimitive) -
        (firstCorrection - secondCorrection) (data - secondBase) + firstCorrection (firstBase - secondBase) := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  abel

theorem norm_affine_parameter_coordinate_difference_le
    (data firstBase secondBase firstPrimitive secondPrimitive : Space)
    (firstCorrection secondCorrection : Space →L[ℝ] Space)
    {constant epsilon size : ℝ} (constantNonnegative : 0 ≤ constant)
    (epsilonNonnegative : 0 ≤ epsilon) (sizeNonnegative : 0 ≤ size)
    (primitiveDifference : ‖firstPrimitive - secondPrimitive‖ ≤ constant * epsilon * size)
    (correctionDifference : ‖firstCorrection - secondCorrection‖ ≤ constant * epsilon * size)
    (correctionBound : ‖firstCorrection‖ ≤ constant * epsilon)
    (baseDifference : ‖firstBase - secondBase‖ ≤ constant * size) :
    ‖(data - firstPrimitive - firstCorrection (data - firstBase)) -
        (data - secondPrimitive - secondCorrection (data - secondBase))‖ ≤
      (constant * (2 + constant)) * epsilon * (1 + ‖data - secondBase‖) * size := by
  rw [affine_parameter_coordinate_difference]
  have firstBound := (firstCorrection - secondCorrection).le_opNorm (data - secondBase)
  have secondBound := firstCorrection.le_opNorm (firstBase - secondBase)
  have firstTriangle : ‖-(firstPrimitive - secondPrimitive) -
      (firstCorrection - secondCorrection) (data - secondBase)‖ ≤
      ‖firstPrimitive - secondPrimitive‖ + ‖(firstCorrection - secondCorrection) (data - secondBase)‖ := by
    simpa only [norm_neg] using (norm_sub_le (-(firstPrimitive - secondPrimitive))
      ((firstCorrection - secondCorrection) (data - secondBase)))
  calc
    _ ≤ (‖firstPrimitive - secondPrimitive‖ +
        ‖(firstCorrection - secondCorrection) (data - secondBase)‖) +
        ‖firstCorrection (firstBase - secondBase)‖ := by
      exact (norm_add_le _ _).trans (add_le_add_right firstTriangle _)
    _ ≤ constant * epsilon * size +
        (constant * epsilon * size) * ‖data - secondBase‖ +
        (constant * epsilon) * (constant * size) := by
      apply add_le_add
      · exact add_le_add primitiveDifference (firstBound.trans
          (mul_le_mul_of_nonneg_right correctionDifference (norm_nonneg _)))
      · exact secondBound.trans (mul_le_mul correctionBound baseDifference (norm_nonneg _) (by positivity))
    _ ≤ _ := by
      have leftover : 0 ≤ constant * epsilon * size * (1 + (1 + constant) * ‖data - secondBase‖) := by positivity
      nlinarith only [leftover]

end EulerNonuniqueness.General
