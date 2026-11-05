import EulerNonuniqueness.Section6.PatchShapeForcing

noncomputable section

namespace EulerNonuniqueness.Section6

theorem forcedCoupledQuadrupole_strain_shape_equation {count : ℕ}
    (coefficients : Fin count → ℝ) (trajectory : ℝ → FiniteQuadrupoleConfiguration count)
    (residual : FiniteQuadrupoleConfiguration count) (block : Fin count) (time : ℝ) (center : ℂ)
    (equation : HasDerivAt trajectory
      (finitePointField (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2)
        (trajectory time) + residual) time)
    (centralNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart (quadrupoleBlock (trajectory time) block)).1
      (fourPointOddPart (quadrupoleBlock (trajectory time) block)).2))
    (normOrder : ‖(fourPointOddPart (quadrupoleBlock (trajectory time) block)).2‖ <
      ‖(fourPointOddPart (quadrupoleBlock (trajectory time) block)).1‖)
    (centerNoncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source,
      center - trajectory time (sourceBlock, source) ≠ 0) :
    let positions := quadrupoleBlock (trajectory time) block
    let point := fourPointOddPart positions
    let field := quadrupoleBlockExternalField coefficients (trajectory time) block
    let strain := quadrupoleBlockExternalStrain coefficients (trajectory time) block center
    let remainder := fourPointOddInternalError (coefficients block) positions +
      fourPointOddPart (fourPointExternalTaylorRemainder field center (fderiv ℝ field center) positions) +
      fourPointOddPart (quadrupoleBlock residual block)
    HasDerivAt (fourPointLocalShapeChart (fun current => quadrupoleBlock (trajectory current) block) time)
      (shapeChartVelocity (coefficients block / (‖point.1‖ ^ 2 - ‖point.2‖ ^ 2))
          (pointShapeChart point.1 point.2) +
        pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2) +
        pointShapeForcing point.1 point.2 remainder.1 remainder.2) time := by
  let positions := quadrupoleBlock (trajectory time) block
  let point := fourPointOddPart positions
  let field := quadrupoleBlockExternalField coefficients (trajectory time) block
  let strain := quadrupoleBlockExternalStrain coefficients (trajectory time) block center
  let remainder := fourPointOddInternalError (coefficients block) positions +
    fourPointOddPart (fourPointExternalTaylorRemainder field center (fderiv ℝ field center) positions) +
    fourPointOddPart (quadrupoleBlock residual block)
  have actual := forcedCoupledQuadrupole_shape_equation coefficients trajectory residual block time
    equation centralNoncollision normOrder
  have decomposition := forcedQuadrupole_odd_strain_decomposition coefficients (trajectory time)
    block center (quadrupoleBlock residual block) centerNoncollision
  change fourPointTotalOddForcing (coefficients block) positions
    ((fun target => field (positions target)) + quadrupoleBlock residual block) =
      (strain * star point.1, strain * star point.2) + remainder at decomposition
  change HasDerivAt _ (shapeChartVelocity _ (pointShapeChart point.1 point.2) +
    pointShapeForcing point.1 point.2
      (fourPointTotalOddForcing (coefficients block) positions
        ((fun target => field (positions target)) + quadrupoleBlock residual block)).1
      (fourPointTotalOddForcing (coefficients block) positions
        ((fun target => field (positions target)) + quadrupoleBlock residual block)).2) time at actual
  rw [decomposition] at actual
  simp only [Prod.fst_add, Prod.snd_add, pointShapeForcing_add] at actual
  convert actual using 1
  dsimp only
  exact add_assoc _ _ _

end EulerNonuniqueness.Section6
