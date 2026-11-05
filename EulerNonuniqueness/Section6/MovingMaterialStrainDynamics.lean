import EulerNonuniqueness.Section6.PaperCentroidStrainForcing

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_coherent_strain_equation {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time radius : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (distance : Fin count → ℝ) (center : ℂ) (radiusNonnegative : 0 ≤ radius)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ family.patchMotion.domain time source patch,
      distance source ≤ ‖center - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source)
    (positionsBound : ∀ patch, ‖patchCentroid family.patchMotion time index patch - center‖ ≤ radius) :
    let positions := fun patch => patchCentroid family.patchMotion time index patch
    let point := Section6.fourPointOddPart positions
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let strain := Section6.vorticityComplexStrain (externalPatchVorticity scales family.patchMotion time index) center
    Section6.FourPointNoncollision (Section6.centrallySymmetricFourPoint point.1 point.2) →
    ‖point.2‖ < ‖point.1‖ →
    |(Section6.pointShapeChart point.1 point.2).1| + |(Section6.pointShapeChart point.1 point.2).2| ≤ 1 / 4 →
    ∃ remainder : ℝ × ℝ,
      HasDerivAt (fun current => Section6.pointShapeChart
          (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index))
        (Section6.shapeChartVelocity (coefficient / diagonalDifference family.patchMotion time index)
            (Section6.pointShapeChart point.1 point.2) +
          Section6.pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2) + remainder) time ∧
      ‖remainder‖ ≤
        ‖Section6.pointShapeForcing point.1 point.2
          (Section6.fourPointOddInternalError coefficient positions).1
          (Section6.fourPointOddInternalError coefficient positions).2‖ +
        Section6.pointShapeForcingWeight point *
          ‖fun patch => quadrupoleInternalPatchResidual scales family.patchMotion time index patch +
            quadrupoleExternalReceiverResidual scales family.patchMotion time index patch‖ +
        Section6.pointShapeForcingWeight point *
          (∑ source ∈ Finset.univ.erase index,
            4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 := by
  dsimp only
  intro noncollision normOrder small
  let positions := fun patch => patchCentroid family.patchMotion time index patch
  let point := Section6.fourPointOddPart positions
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let forcing := Section6.fourPointTotalOddForcing coefficient positions
    (quadrupoleCentroidForcing scales family.patchMotion time index)
  let strain := Section6.vorticityComplexStrain (externalPatchVorticity scales family.patchMotion time index) center
  let strainShape := Section6.pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2)
  refine ⟨Section6.pointShapeForcing point.1 point.2 forcing.1 forcing.2 - strainShape, ?_, ?_⟩
  · have derivative := family.centroid_coherent_shape_equation_of_small evolution inside index pathInside material
      noncollision normOrder small
    apply derivative.congr_deriv
    dsimp only [strainShape, forcing, strain, point, positions, coefficient, diagonalDifference,
      positiveHalfDiagonal, negativeHalfDiagonal, Section6.fourPointOddPart]
    abel
  · exact evolution.quadrupoleCentroidForcing_strain_remainder_bound inside amplitudePositive frequencyPositive
      ratioPositive index distance center radiusNonnegative positive separated near positionsBound

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
