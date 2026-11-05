import EulerNonuniqueness.General.MovingQuadraticDerivative
import EulerNonuniqueness.General.CubicFiberCoefficient

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Parameter : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

local instance movingParameterOperatorGroup : NormedAddCommGroup (Parameter →L[ℝ] BilinearEnd Space) :=
  ContinuousLinearMap.toNormedAddCommGroup

theorem moving_quadratic_parameter_difference_norm_le
    (first second : Parameter →L[ℝ] BilinearEnd Space)
    (firstVelocity secondVelocity : Parameter) (initial final : Space) :
    ‖first firstVelocity initial initial - second secondVelocity final final‖ ≤
      ‖first‖ * ‖firstVelocity - secondVelocity‖ * ‖initial‖ ^ 2 +
        ‖first‖ * ‖secondVelocity‖ * (‖initial‖ + ‖final‖) * ‖initial - final‖ +
        ‖first - second‖ * ‖secondVelocity‖ * ‖final‖ ^ 2 := by
  have bilinearBound (operator : BilinearEnd Space) (left right : Space) :
      ‖operator left right‖ ≤ ‖operator‖ * ‖left‖ * ‖right‖ :=
    (operator left).le_opNorm right |>.trans
      (mul_le_mul_of_nonneg_right (operator.le_opNorm left) (norm_nonneg right))
  have firstBound : ‖first (firstVelocity - secondVelocity) initial initial‖ ≤
      ‖first‖ * ‖firstVelocity - secondVelocity‖ * ‖initial‖ ^ 2 := by
    calc
      _ ≤ ‖first (firstVelocity - secondVelocity)‖ * ‖initial‖ * ‖initial‖ := bilinearBound _ _ _
      _ ≤ (‖first‖ * ‖firstVelocity - secondVelocity‖) * ‖initial‖ * ‖initial‖ := by gcongr; exact first.le_opNorm _
      _ = _ := by ring
  have secondBound : ‖first secondVelocity (initial - final) initial‖ +
      ‖first secondVelocity final (initial - final)‖ ≤
      ‖first‖ * ‖secondVelocity‖ * (‖initial‖ + ‖final‖) * ‖initial - final‖ := by
    calc
      _ ≤ ‖first secondVelocity‖ * ‖initial - final‖ * ‖initial‖ +
          ‖first secondVelocity‖ * ‖final‖ * ‖initial - final‖ := add_le_add (bilinearBound _ _ _) (bilinearBound _ _ _)
      _ = ‖first secondVelocity‖ * (‖initial‖ + ‖final‖) * ‖initial - final‖ := by ring
      _ ≤ _ := by gcongr; exact first.le_opNorm _
  have thirdBound : ‖(first - second) secondVelocity final final‖ ≤
      ‖first - second‖ * ‖secondVelocity‖ * ‖final‖ ^ 2 := by
    calc
      _ ≤ ‖(first - second) secondVelocity‖ * ‖final‖ * ‖final‖ := bilinearBound _ _ _
      _ ≤ (‖first - second‖ * ‖secondVelocity‖) * ‖final‖ * ‖final‖ := by gcongr; exact (first - second).le_opNorm _
      _ = _ := by ring
  have identity : first firstVelocity initial initial - second secondVelocity final final =
      first (firstVelocity - secondVelocity) initial initial +
        (first secondVelocity (initial - final) initial + first secondVelocity final (initial - final)) +
        (first - second) secondVelocity final final := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add firstBound ((norm_add_le _ _).trans secondBound))) thirdBound)

end

end EulerNonuniqueness.General
