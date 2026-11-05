import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics
import EulerNonuniqueness.Section6.SelectedPatchShapeDynamics
import EulerNonuniqueness.Section6.ReferenceShapeChartDomain

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

def quadrupoleCentroidForcing {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) : ℂ :=
  biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch) +
    quadrupoleInternalPatchResidual scales motion time index patch +
    quadrupoleExternalReceiverResidual scales motion time index patch

namespace FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroid_coherent_shape_equation (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) :
    let trajectory := fun (current : ℝ) (patch : Fin 4) => Paper.patchCentroid family.patchMotion current index patch
    let positions := trajectory time
    let point := Section6.fourPointOddPart positions
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let forcing := quadrupoleCentroidForcing scales family.patchMotion time index
    Section6.FourPointNoncollision (Section6.centrallySymmetricFourPoint point.1 point.2) →
    ‖point.2‖ < ‖point.1‖ → ((point.2 / point.1) ^ 2).re < 0 →
    HasDerivAt (fun current => Section6.pointShapeChart
        (Section6.fourPointOddPart (trajectory current)).1 (Section6.fourPointOddPart (trajectory current)).2)
      (Section6.shapeChartVelocity (coefficient / (‖point.1‖ ^ 2 - ‖point.2‖ ^ 2))
          (Section6.pointShapeChart point.1 point.2) +
        Section6.pointShapeForcing point.1 point.2
          (Section6.fourPointTotalOddForcing coefficient positions forcing).1
          (Section6.fourPointTotalOddForcing coefficient positions forcing).2) time := by
  dsimp only
  intro noncollision normOrder left
  apply Section6.fourPointShapeChart_actual_forced_equation
    (trajectory := fun (current : ℝ) (patch : Fin 4) => Paper.patchCentroid family.patchMotion current index patch)
    (forcing := quadrupoleCentroidForcing scales family.patchMotion time index) noncollision normOrder left
  intro patch
  simpa only [quadrupoleCentroidForcing, add_assoc] using
    family.patchCentroid_hasDerivAt_point_field evolution inside index patch (pathInside patch) (material patch)

theorem centroid_coherent_shape_equation_of_small (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) :
    let trajectory := fun (current : ℝ) (patch : Fin 4) => Paper.patchCentroid family.patchMotion current index patch
    let positions := trajectory time
    let point := Section6.fourPointOddPart positions
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let forcing := quadrupoleCentroidForcing scales family.patchMotion time index
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
  exact family.centroid_coherent_shape_equation evolution inside index pathInside material noncollision normOrder
    (Section6.pointShapeChart_leftHalfPlane_of_small positiveNonzero negativeNonzero small)

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
