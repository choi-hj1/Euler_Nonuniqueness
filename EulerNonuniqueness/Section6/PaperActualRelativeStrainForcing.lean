import EulerNonuniqueness.Section6.PaperRelativeShapeForcingSplit
import EulerNonuniqueness.Section6.RelativeShapeForcingOperatorBudget
import EulerNonuniqueness.Section6.RelativeNormalFormForcingOperator

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleRelativeLeadingStrain {count : ℕ} (scales : Scales)
    (alternative reference : PatchMotion count) (time : ℝ) (index : Fin count) : ℝ × ℝ :=
  pointShapeForcingCLM (positiveHalfDiagonal reference time index, negativeHalfDiagonal reference time index)
    (complexStrainPair (quadrupoleExternalShapeStrain scales alternative time index -
      quadrupoleExternalShapeStrain scales reference time index)
      (positiveHalfDiagonal reference time index, negativeHalfDiagonal reference time index))

theorem referencePointShapeForcing_relative_actual_strain_bound {count : ℕ} (scales : Scales)
    (alternative reference : PatchMotion count) (time : ℝ) (index : Fin count) :
    ‖referencePointShapeForcing scales alternative time index - referencePointShapeForcing scales reference time index -
        quadrupoleRelativeLeadingStrain scales alternative reference time index‖ ≤
      pointShapeForcingWeight (positiveHalfDiagonal reference time index, negativeHalfDiagonal reference time index) *
        (‖fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
              (fun patch => patchCentroid alternative time index patch) -
            fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
              (fun patch => patchCentroid reference time index patch)‖ +
          ‖quadrupoleShapeCentroidResidual scales alternative time index - quadrupoleShapeCentroidResidual scales reference time index‖ +
          ‖quadrupoleExternalTaylorResidual scales alternative time index - quadrupoleExternalTaylorResidual scales reference time index‖ +
          ‖quadrupoleExternalShapeStrain scales alternative time index‖ *
            ‖(positiveHalfDiagonal alternative time index, negativeHalfDiagonal alternative time index) -
              (positiveHalfDiagonal reference time index, negativeHalfDiagonal reference time index)‖) +
      pointShapeForcingOperatorVariation
          (positiveHalfDiagonal alternative time index, negativeHalfDiagonal alternative time index)
          (positiveHalfDiagonal reference time index, negativeHalfDiagonal reference time index) *
        ‖complexStrainPair (quadrupoleExternalShapeStrain scales alternative time index)
            (positiveHalfDiagonal alternative time index, negativeHalfDiagonal alternative time index) +
          quadrupoleShapeForcingRemainder scales alternative time index‖ := by
  rw [referencePointShapeForcing_strain_remainder_identity,
    referencePointShapeForcing_strain_remainder_identity]
  exact (relative_pointShapeForcing_leading_strain_bound _ _ _ _ _ _).trans
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (add_le_add_right (quadrupoleShapeForcingRemainder_relative_bound scales alternative reference time index) _)
        (pointShapeForcingWeight_nonnegative _))
      (mul_le_mul_of_nonneg_right (pointShapeForcingCLM_difference_norm_le _ _) (norm_nonneg _)))

theorem referenceStraightenedForcing_relative_actual_strain_bound {count : ℕ} (scales : Scales)
    (alternative reference : PatchMotion count) (graph coordinate : ℝ → ℝ) (time : ℝ) (index : Fin count) :
    let alternativePoint := (positiveHalfDiagonal alternative time index, negativeHalfDiagonal alternative time index)
    let referencePoint := (positiveHalfDiagonal reference time index, negativeHalfDiagonal reference time index)
    let leading := quadrupoleRelativeLeadingStrain scales alternative reference time index
    ‖referenceStraightenedForcing scales alternative graph coordinate index time -
        referenceStraightenedForcing scales reference graph coordinate index time - leading‖ ≤
      (1 + |deriv coordinate (unstableShape reference time index)| + |deriv graph (unstableShape reference time index)|) *
        (pointShapeForcingWeight referencePoint *
          (‖quadrupoleShapeForcingRemainder scales alternative time index - quadrupoleShapeForcingRemainder scales reference time index‖ +
            ‖quadrupoleExternalShapeStrain scales alternative time index‖ * ‖alternativePoint - referencePoint‖) +
          pointShapeForcingOperatorVariation alternativePoint referencePoint *
            ‖complexStrainPair (quadrupoleExternalShapeStrain scales alternative time index) alternativePoint +
              quadrupoleShapeForcingRemainder scales alternative time index‖) +
      (|deriv coordinate (unstableShape reference time index) - 1| + |deriv graph (unstableShape reference time index)|) * ‖leading‖ +
      (|deriv coordinate (unstableShape alternative time index) - deriv coordinate (unstableShape reference time index)| +
        |deriv graph (unstableShape alternative time index) - deriv graph (unstableShape reference time index)|) *
          ‖referencePointShapeForcing scales alternative time index‖ := by
  dsimp only
  apply (referenceStraightenedForcing_relative_leading_bound scales alternative reference graph coordinate index time _).trans
  apply add_le_add_right
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [referencePointShapeForcing_strain_remainder_identity,
    referencePointShapeForcing_strain_remainder_identity]
  exact (relative_pointShapeForcing_leading_strain_bound _ _ _ _ _ _).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right (pointShapeForcingCLM_difference_norm_le _ _) (norm_nonneg _)) _)

end EulerNonuniqueness.Paper
