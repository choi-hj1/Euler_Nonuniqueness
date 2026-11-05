import EulerNonuniqueness.Section6.PaperRelativeShapeForcingSplit

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem quadrupoleTotalOddForcing_eq_strain_remainder {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) :
    fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing scales motion time index) =
      complexStrainPair (quadrupoleExternalShapeStrain scales motion time index)
          (positiveHalfDiagonal motion time index, negativeHalfDiagonal motion time index) +
        quadrupoleShapeForcingRemainder scales motion time index := by
  let positions := fun patch => patchCentroid motion time index patch
  let field := biotSavart (externalPatchVorticity scales motion time index)
  have forcingIdentity : quadrupoleCentroidForcing scales motion time index =
      (fun patch => field (positions patch)) + quadrupoleShapeCentroidResidual scales motion time index := by
    ext patch
    dsimp only [quadrupoleCentroidForcing, quadrupoleShapeCentroidResidual, Pi.add_apply, field, positions]
    abel
  have taylor := fourPointOddPart_antilinear_taylor field (quadrupoleCenter motion time index)
    (quadrupoleExternalShapeStrain scales motion time index) positions
  rw [forcingIdentity, fourPointTotalOddForcing, fourPointOddPart_add, taylor]
  change _ = complexStrainPair (quadrupoleExternalShapeStrain scales motion time index) (fourPointOddPart positions) +
    (fourPointOddInternalError _ positions + fourPointOddPart (quadrupoleShapeCentroidResidual scales motion time index) +
      fourPointOddPart (quadrupoleExternalTaylorResidual scales motion time index))
  dsimp only [complexStrainPair, quadrupoleShapeForcingRemainder, quadrupoleExternalTaylorResidual,
    quadrupoleExternalShapeStrain, field, positions]
  abel

end EulerNonuniqueness.Paper
