import EulerNonuniqueness.Section6.SelectedPatchShapeDynamics
import EulerNonuniqueness.Section6.ActualQuadrupolePatchDynamics
import EulerNonuniqueness.Section6.ReferenceShapeChartDomain

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

theorem separatedDisk_centroid_coherent_shape_equation {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖)
    (flow : FiniteLiteralPatchFlow
      (separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separation))
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (block : Fin count) :
    let labels := fun target : Fin 4 => finProdFinEquiv (block, target)
    let trajectory := fun (current : ℝ) (target : Fin 4) => flow.centroid current (labels target)
    let positions := trajectory time
    let point := Section6.fourPointOddPart positions
    let coefficient := scales.omega (block.val + 1) * scales.length (block.val + 1) ^ 2
    let forcing := fun target =>
      flow.subfamilyExternalPatchField (Finset.univ.image labels) time (positions target) +
        flow.subfamilyInternalDeformationResidual (Finset.univ.image labels) time (labels target) +
        flow.subfamilyExternalReceiverResidual (Finset.univ.image labels) time (labels target)
    Section6.FourPointNoncollision (Section6.centrallySymmetricFourPoint point.1 point.2) →
    ‖point.2‖ < ‖point.1‖ →
    |(Section6.pointShapeChart point.1 point.2).1| + |(Section6.pointShapeChart point.1 point.2).2| ≤ 1 / 4 →
    HasDerivAt (fun current => Section6.pointShapeChart
        (Section6.fourPointOddPart (trajectory current)).1 (Section6.fourPointOddPart (trajectory current)).2)
      (Section6.shapeChartVelocity (coefficient / (‖point.1‖ ^ 2 - ‖point.2‖ ^ 2))
          (Section6.pointShapeChart point.1 point.2) +
        Section6.pointShapeForcing point.1 point.2
          (Section6.fourPointTotalOddForcing coefficient positions forcing).1
          (Section6.fourPointTotalOddForcing coefficient positions forcing).2) time := by
  dsimp only
  intro noncollision normOrder small
  obtain ⟨positiveNonzero, negativeNonzero, _, _⟩ :=
    Section6.centrallySymmetricFourPoint_noncollision_conditions noncollision
  apply flow.selected_centroid_coherent_shape_equation
    (fun target : Fin 4 => finProdFinEquiv (block, target))
    (fun first second equality => (Prod.mk.inj (finProdFinEquiv.injective equality)).2)
    (scales.omega (block.val + 1) * scales.length (block.val + 1) ^ 2)
    (fun target => separatedDiskConfiguration_point_coefficient scales amplitudePositive
      frequencyPositive ratioPositive centers separation block target) inside noncollision normOrder
  exact Section6.pointShapeChart_leftHalfPlane_of_small positiveNonzero negativeNonzero small

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
