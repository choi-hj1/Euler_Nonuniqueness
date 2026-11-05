import EulerNonuniqueness.Section6.RelativeShapeForcingOperatorBudget
import EulerNonuniqueness.Section4.ReferenceComputedShapeEquation

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem referencePointShapeForcing_relative_raw_bound {count : ℕ} (scales : Scales)
    (first second : PatchMotion count) (time : ℝ) (index : Fin count) :
    let pointFirst := (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index)
    let pointSecond := (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index)
    let forcingFirst := fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid first time index patch) (quadrupoleCentroidForcing scales first time index)
    let forcingSecond := fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid second time index patch) (quadrupoleCentroidForcing scales second time index)
    ‖referencePointShapeForcing scales first time index - referencePointShapeForcing scales second time index‖ ≤
      pointShapeForcingWeight pointSecond * ‖forcingFirst - forcingSecond‖ +
        pointShapeForcingOperatorVariation pointFirst pointSecond * ‖forcingFirst‖ := by
  dsimp only
  let firstPoint := (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index)
  let secondPoint := (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index)
  let firstForce := fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun patch => patchCentroid first time index patch) (quadrupoleCentroidForcing scales first time index)
  let secondForce := fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun patch => patchCentroid second time index patch) (quadrupoleCentroidForcing scales second time index)
  have actual := (pointShapeForcingCLM_relative_bound firstPoint secondPoint firstForce secondForce).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right (pointShapeForcingCLM_difference_norm_le firstPoint secondPoint)
      (norm_nonneg firstForce)) _)
  change ‖pointShapeForcing firstPoint.1 firstPoint.2 firstForce.1 firstForce.2 -
    pointShapeForcing secondPoint.1 secondPoint.2 secondForce.1 secondForce.2‖ ≤
      pointShapeForcingWeight secondPoint * ‖firstForce - secondForce‖ +
        pointShapeForcingOperatorVariation firstPoint secondPoint * ‖firstForce‖
  exact actual

end EulerNonuniqueness.Paper
