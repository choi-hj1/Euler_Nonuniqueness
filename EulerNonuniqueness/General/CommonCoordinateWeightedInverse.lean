import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def weightedProjectionDistance (transverse neutral : Space →L[ℝ] Space) (weight : ℝ)
    (first final : Space) : ℝ :=
  ‖transverse (first - final)‖ + weight * ‖neutral (first - final)‖

theorem weightedProjectionDistance_common_coordinate_inverse
    (transverse neutral : Space →L[ℝ] Space) (first final correctedFirst correctedFinal : Space)
    {weight deviation : ℝ} (weightNonnegative : 0 ≤ weight) (weightSmall : weight ≤ 1)
    (deviationNonnegative : 0 ≤ deviation)
    (small : (‖transverse‖ + ‖neutral‖) * deviation ≤ weight / 2)
    (correction : ‖(correctedFirst - first) - (correctedFinal - final)‖ ≤
      deviation * (‖transverse (first - final)‖ + ‖neutral (first - final)‖)) :
    weightedProjectionDistance transverse neutral weight first final ≤
      2 * weightedProjectionDistance transverse neutral weight correctedFirst correctedFinal := by
  let error := (correctedFirst - first) - (correctedFinal - final)
  have identity : first - final = (correctedFirst - correctedFinal) - error := by dsimp [error]; abel
  have transverseBound : ‖transverse (first - final)‖ ≤
      ‖transverse (correctedFirst - correctedFinal)‖ + ‖transverse‖ * ‖error‖ := by
    conv_lhs => rw [identity, map_sub]
    exact (norm_sub_le _ _).trans (add_le_add_left (transverse.le_opNorm error) _)
  have neutralBound : ‖neutral (first - final)‖ ≤
      ‖neutral (correctedFirst - correctedFinal)‖ + ‖neutral‖ * ‖error‖ := by
    conv_lhs => rw [identity, map_sub]
    exact (norm_sub_le _ _).trans (add_le_add_left (neutral.le_opNorm error) _)
  have paired := add_le_add transverseBound (mul_le_mul_of_nonneg_left neutralBound weightNonnegative)
  have operatorBound : ‖transverse‖ + weight * ‖neutral‖ ≤ ‖transverse‖ + ‖neutral‖ := by
    nlinarith [norm_nonneg neutral]
  have errorBound : (‖transverse‖ + weight * ‖neutral‖) * ‖error‖ ≤
      (‖transverse‖ + ‖neutral‖) * deviation *
        (‖transverse (first - final)‖ + ‖neutral (first - final)‖) := by
    have numerical := mul_le_mul operatorBound correction (norm_nonneg error)
      (add_nonneg (norm_nonneg transverse) (norm_nonneg neutral))
    exact numerical.trans_eq (by ring)
  have smallBound := mul_le_mul_of_nonneg_right small
    (add_nonneg (norm_nonneg (transverse (first - final))) (norm_nonneg (neutral (first - final))))
  have weightedSmall : weight / 2 * (‖transverse (first - final)‖ + ‖neutral (first - final)‖) ≤
      (‖transverse (first - final)‖ + weight * ‖neutral (first - final)‖) / 2 := by
    nlinarith [norm_nonneg (transverse (first - final))]
  dsimp only [weightedProjectionDistance]
  nlinarith [errorBound.trans (smallBound.trans weightedSmall)]

end EulerNonuniqueness.General
