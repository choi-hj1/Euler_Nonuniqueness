import EulerNonuniqueness.Section6.ActualPointStrainForcing

noncomputable section

namespace EulerNonuniqueness.Section6

theorem coupledQuadrupole_actual_shape_equation {count : ℕ}
    (coefficients : Fin count → ℝ) (trajectory : ℝ → FiniteQuadrupoleConfiguration count)
    (block : Fin count) (time : ℝ) (center : ℂ)
    (equation : HasDerivAt trajectory
      (finitePointField (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2)
        (trajectory time)) time)
    (centralNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart (quadrupoleBlock (trajectory time) block)).1
      (fourPointOddPart (quadrupoleBlock (trajectory time) block)).2))
    (normOrder : ‖(fourPointOddPart (quadrupoleBlock (trajectory time) block)).2‖ <
      ‖(fourPointOddPart (quadrupoleBlock (trajectory time) block)).1‖)
    (centerNoncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source,
      center - trajectory time (sourceBlock, source) ≠ 0) :
    let positions := quadrupoleBlock (trajectory time) block
    let point := fourPointOddPart positions
    let strain := quadrupoleBlockExternalStrain coefficients (trajectory time) block center
    let remainder := fourPointOddInternalError (coefficients block) positions +
      fourPointOddPart (fourPointExternalTaylorRemainder
        (quadrupoleBlockExternalField coefficients (trajectory time) block) center
        (fderiv ℝ (quadrupoleBlockExternalField coefficients (trajectory time) block) center) positions)
    HasDerivAt (fourPointLocalShapeChart (fun current => quadrupoleBlock (trajectory current) block) time)
      (shapeChartVelocity (coefficients block / (‖point.1‖ ^ 2 - ‖point.2‖ ^ 2))
          (pointShapeChart point.1 point.2) +
        pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2) +
        pointShapeForcing point.1 point.2 remainder.1 remainder.2) time := by
  let positions := quadrupoleBlock (trajectory time) block
  let point := fourPointOddPart positions
  let strain := quadrupoleBlockExternalStrain coefficients (trajectory time) block center
  let field := quadrupoleBlockExternalField coefficients (trajectory time) block
  let forcing := fun target => field (positions target)
  let remainder := fourPointOddInternalError (coefficients block) positions +
    fourPointOddPart (fourPointExternalTaylorRemainder field center (fderiv ℝ field center) positions)
  have blockEquation := coupledQuadrupole_block_hasDerivAt equation block
  have actual := fourPointLocalShapeChart_actual_equation
    (trajectory := fun current => quadrupoleBlock (trajectory current) block)
    (coefficient := coefficients block) (time := time) (forcing := forcing)
    centralNoncollision normOrder blockEquation
  have oddIdentity := quadrupoleBlockExternalField_odd_taylor coefficients (trajectory time) block center positions centerNoncollision
  have forcingIdentity : fourPointTotalOddForcing (coefficients block) positions forcing =
      (strain * star point.1, strain * star point.2) + remainder := by
    change fourPointOddInternalError (coefficients block) positions + fourPointOddPart forcing = _
    change fourPointOddInternalError (coefficients block) positions +
      fourPointOddPart (fun target => quadrupoleBlockExternalField coefficients (trajectory time) block (positions target)) = _
    rw [oddIdentity]
    dsimp [remainder, strain, point, field]
    abel
  have shapeForcingIdentity : pointShapeForcing point.1 point.2
      (fourPointTotalOddForcing (coefficients block) positions forcing).1
      (fourPointTotalOddForcing (coefficients block) positions forcing).2 =
      pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2) +
        pointShapeForcing point.1 point.2 remainder.1 remainder.2 := by
    rw [forcingIdentity]
    exact pointShapeForcing_add _ _ _ _ _ _
  change HasDerivAt _ (shapeChartVelocity _ (pointShapeChart point.1 point.2) +
    pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2) +
    pointShapeForcing point.1 point.2 remainder.1 remainder.2) time
  convert actual using 1
  change _ = shapeChartVelocity _ (pointShapeChart point.1 point.2) +
    pointShapeForcing point.1 point.2
      (fourPointTotalOddForcing (coefficients block) positions forcing).1
      (fourPointTotalOddForcing (coefficients block) positions forcing).2
  rw [shapeForcingIdentity]
  abel

end EulerNonuniqueness.Section6
