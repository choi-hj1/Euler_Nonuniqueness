import EulerNonuniqueness.Section6.ReferenceChartAnnulus
import EulerNonuniqueness.Section6.MovingMaterialShapeDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_coherent_shape_equation_of_reference_chart {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (small : |(Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
        (negativeHalfDiagonal family.patchMotion time index)).1| +
      |(Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
        (negativeHalfDiagonal family.patchMotion time index)).2| ≤ 1 / 4) :
    let positions := fun patch => patchCentroid family.patchMotion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    HasDerivAt (fun current => Section6.pointShapeChart
        (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index))
      (Section6.shapeChartVelocity (coefficient / diagonalDifference family.patchMotion time index)
          (Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
            (negativeHalfDiagonal family.patchMotion time index)) +
        Section6.pointShapeForcing (positiveHalfDiagonal family.patchMotion time index)
          (negativeHalfDiagonal family.patchMotion time index)
          (Section6.fourPointTotalOddForcing coefficient positions
            (quadrupoleCentroidForcing scales family.patchMotion time index)).1
          (Section6.fourPointTotalOddForcing coefficient positions
            (quadrupoleCentroidForcing scales family.patchMotion time index)).2) time := by
  let positive := positiveHalfDiagonal family.patchMotion time index
  let negative := negativeHalfDiagonal family.patchMotion time index
  obtain ⟨positiveNonzero, negativeNonzero, _, ratioUpper⟩ :=
    Section6.pointShapeChart_reference_annulus positive negative small
  have normPositive : 0 < ‖positive‖ := norm_pos_iff.mpr positiveNonzero
  have normOrder : ‖negative‖ < ‖positive‖ := by
    have bounded := (div_le_iff₀ normPositive).mp ratioUpper
    nlinarith
  have differenceNonzero : positive - negative ≠ 0 := by
    intro zero
    have equality := sub_eq_zero.mp zero
    rw [equality] at normOrder
    exact (lt_irrefl _ normOrder)
  have sumNonzero : positive + negative ≠ 0 := by
    intro zero
    have equality : negative = -positive := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    rw [equality, norm_neg] at normOrder
    exact (lt_irrefl _ normOrder)
  have noncollision := Section6.centrallySymmetricFourPoint_noncollision
    positiveNonzero negativeNonzero differenceNonzero sumNonzero
  exact family.centroid_coherent_shape_equation_of_small evolution inside index pathInside material
    noncollision normOrder small

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
