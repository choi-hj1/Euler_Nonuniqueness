import EulerNonuniqueness.Section6.RelativeShapeForcingOperator
import EulerNonuniqueness.Section6.PaperRelativeExteriorTaylorResidual
import EulerNonuniqueness.Section4.ReferenceComputedShapeEquation

noncomputable section

namespace EulerNonuniqueness.Section6

def complexStrainPair (strain : ℂ) (point : ℂ × ℂ) : ℂ × ℂ :=
  (strain * star point.1, strain * star point.2)

theorem complexStrainPair_norm (strain : ℂ) (point : ℂ × ℂ) :
    ‖complexStrainPair strain point‖ = ‖strain‖ * ‖point‖ := by
  change ‖strain • (star point.1, star point.2)‖ = _
  rw [norm_smul]
  simp only [Prod.norm_def, norm_star]

theorem complexStrainPair_relative (firstStrain secondStrain : ℂ) (firstPoint secondPoint : ℂ × ℂ) :
    complexStrainPair firstStrain firstPoint - complexStrainPair secondStrain secondPoint =
      complexStrainPair (firstStrain - secondStrain) secondPoint + complexStrainPair firstStrain (firstPoint - secondPoint) := by
  ext <;> simp only [complexStrainPair, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, star_sub] <;> ring

theorem relative_pointShapeForcing_leading_strain_identity
    (firstPoint secondPoint firstRemainder secondRemainder : ℂ × ℂ) (firstStrain secondStrain : ℂ) :
    pointShapeForcingCLM firstPoint (complexStrainPair firstStrain firstPoint + firstRemainder) -
        pointShapeForcingCLM secondPoint (complexStrainPair secondStrain secondPoint + secondRemainder) -
        pointShapeForcingCLM secondPoint (complexStrainPair (firstStrain - secondStrain) secondPoint) =
      pointShapeForcingCLM secondPoint
          (firstRemainder - secondRemainder + complexStrainPair firstStrain (firstPoint - secondPoint)) +
        (pointShapeForcingCLM firstPoint - pointShapeForcingCLM secondPoint)
          (complexStrainPair firstStrain firstPoint + firstRemainder) := by
  have difference : (complexStrainPair firstStrain firstPoint + firstRemainder) -
      (complexStrainPair secondStrain secondPoint + secondRemainder) =
      complexStrainPair (firstStrain - secondStrain) secondPoint +
        (firstRemainder - secondRemainder + complexStrainPair firstStrain (firstPoint - secondPoint)) := by
    rw [add_sub_add_comm, complexStrainPair_relative]
    abel
  rw [pointShapeForcingCLM_relative_identity, difference, map_add]
  abel

theorem relative_pointShapeForcing_leading_strain_bound
    (firstPoint secondPoint firstRemainder secondRemainder : ℂ × ℂ) (firstStrain secondStrain : ℂ) :
    ‖pointShapeForcingCLM firstPoint (complexStrainPair firstStrain firstPoint + firstRemainder) -
        pointShapeForcingCLM secondPoint (complexStrainPair secondStrain secondPoint + secondRemainder) -
        pointShapeForcingCLM secondPoint (complexStrainPair (firstStrain - secondStrain) secondPoint)‖ ≤
      pointShapeForcingWeight secondPoint * (‖firstRemainder - secondRemainder‖ + ‖firstStrain‖ * ‖firstPoint - secondPoint‖) +
        ‖pointShapeForcingCLM firstPoint - pointShapeForcingCLM secondPoint‖ *
          ‖complexStrainPair firstStrain firstPoint + firstRemainder‖ := by
  rw [relative_pointShapeForcing_leading_strain_identity]
  apply (norm_add_le _ _).trans
  have residualNorm := norm_add_le (firstRemainder - secondRemainder) (complexStrainPair firstStrain (firstPoint - secondPoint))
  rw [complexStrainPair_norm] at residualNorm
  have pointBound := ((pointShapeForcingCLM secondPoint).le_opNorm
      (firstRemainder - secondRemainder + complexStrainPair firstStrain (firstPoint - secondPoint))).trans
    (mul_le_mul_of_nonneg_right (pointShapeForcingCLM_norm_le secondPoint)
      (norm_nonneg (firstRemainder - secondRemainder + complexStrainPair firstStrain (firstPoint - secondPoint))))
  exact add_le_add (pointBound.trans (mul_le_mul_of_nonneg_left residualNorm
    (pointShapeForcingWeight_nonnegative secondPoint)))
    ((pointShapeForcingCLM firstPoint - pointShapeForcingCLM secondPoint).le_opNorm _)

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleShapeCentroidResidual {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : FourPointConfiguration :=
  fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
    quadrupoleExternalReceiverResidual scales motion time index patch

def quadrupoleExternalShapeStrain {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℂ :=
  vorticityComplexStrain (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index)

def quadrupoleShapeForcingRemainder {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℂ × ℂ :=
  fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid motion time index patch) +
    fourPointOddPart (quadrupoleShapeCentroidResidual scales motion time index) +
    fourPointOddPart (quadrupoleExternalTaylorResidual scales motion time index)

theorem referencePointShapeForcing_strain_remainder_identity {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) :
    referencePointShapeForcing scales motion time index =
      pointShapeForcingCLM (positiveHalfDiagonal motion time index, negativeHalfDiagonal motion time index)
        (complexStrainPair (quadrupoleExternalShapeStrain scales motion time index)
            (positiveHalfDiagonal motion time index, negativeHalfDiagonal motion time index) +
          quadrupoleShapeForcingRemainder scales motion time index) := by
  let positions := fun patch => patchCentroid motion time index patch
  let field := biotSavart (externalPatchVorticity scales motion time index)
  have forcingIdentity : quadrupoleCentroidForcing scales motion time index =
      (fun patch => field (positions patch)) + quadrupoleShapeCentroidResidual scales motion time index := by
    funext patch
    dsimp only [quadrupoleCentroidForcing, quadrupoleShapeCentroidResidual, Pi.add_apply, field, positions]
    abel
  have taylor := fourPointOddPart_antilinear_taylor field (quadrupoleCenter motion time index)
    (quadrupoleExternalShapeStrain scales motion time index) positions
  change pointShapeForcingCLM (fourPointOddPart positions)
      (fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) positions
        (quadrupoleCentroidForcing scales motion time index)) = _
  rw [forcingIdentity, fourPointTotalOddForcing, fourPointOddPart_add, taylor]
  congr 1
  change _ = complexStrainPair (quadrupoleExternalShapeStrain scales motion time index) (fourPointOddPart positions) +
    (fourPointOddInternalError _ positions + fourPointOddPart (quadrupoleShapeCentroidResidual scales motion time index) +
      fourPointOddPart (quadrupoleExternalTaylorResidual scales motion time index))
  dsimp only [complexStrainPair, quadrupoleExternalTaylorResidual, quadrupoleExternalShapeStrain, field, positions]
  abel

theorem quadrupoleShapeForcingRemainder_relative_bound {count : ℕ} (scales : Scales)
    (first second : PatchMotion count) (time : ℝ) (index : Fin count) :
    ‖quadrupoleShapeForcingRemainder scales first time index - quadrupoleShapeForcingRemainder scales second time index‖ ≤
      ‖fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid first time index patch) -
        fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid second time index patch)‖ +
      ‖quadrupoleShapeCentroidResidual scales first time index - quadrupoleShapeCentroidResidual scales second time index‖ +
      ‖quadrupoleExternalTaylorResidual scales first time index - quadrupoleExternalTaylorResidual scales second time index‖ := by
  have oddSub (first second : FourPointConfiguration) : fourPointOddPart first - fourPointOddPart second = fourPointOddPart (first - second) := by
    ext <;> dsimp only [fourPointOddPart, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply] <;> ring
  rw [quadrupoleShapeForcingRemainder, quadrupoleShapeForcingRemainder, add_sub_add_comm, add_sub_add_comm, oddSub, oddSub]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add_left (fourPointOddPart_norm_le _) _)) (fourPointOddPart_norm_le _))

end EulerNonuniqueness.Paper
