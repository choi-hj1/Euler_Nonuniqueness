import EulerNonuniqueness.Section4.ReferenceComputedShapeEquation

noncomputable section

open Set Filter EulerNonuniqueness.Section6
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_paper_shape_hasDerivAt_of_upper {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (upper : 0 < (negativeHalfDiagonal family.patchMotion time index /
      positiveHalfDiagonal family.patchMotion time index).im)
    (small : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4) :
    HasDerivAt (fun current => (unstableShape family.patchMotion current index, stableShape family.patchMotion current index))
      (referencePointShapeVelocity scales family.patchMotion time index) time := by
  have paper := pointShapeChart_eq_paper_shape_of_upper family.patchMotion time index upper
  have coherentSmall : |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
      (negativeHalfDiagonal family.patchMotion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
        (negativeHalfDiagonal family.patchMotion time index)).2| ≤ 1 / 4 := by rwa [paper]
  have nonzero := (pointShapeChart_reference_annulus _ _ coherentSmall).1
  have centroidContinuous (patch : Fin 4) :=
    (family.patchCentroid_hasDerivAt_point_field evolution inside index patch (pathInside patch) (material patch)).continuousAt
  have positiveContinuous : ContinuousAt (fun current => positiveHalfDiagonal family.patchMotion current index) time :=
    ((centroidContinuous 0).sub (centroidContinuous 1)).div_const 2
  have negativeContinuous : ContinuousAt (fun current => negativeHalfDiagonal family.patchMotion current index) time :=
    ((centroidContinuous 2).sub (centroidContinuous 3)).div_const 2
  have ratioContinuous := negativeContinuous.div positiveContinuous nonzero
  have imaginaryContinuous := Complex.continuous_im.continuousAt.comp ratioContinuous
  have near := imaginaryContinuous.eventually (eventually_gt_nhds upper)
  have actual := family.centroid_coherent_shape_equation_of_reference_chart evolution inside index pathInside material coherentSmall
  dsimp only at actual
  rw [paper] at actual
  change HasDerivAt (fun current => pointShapeChart (positiveHalfDiagonal family.patchMotion current index)
    (negativeHalfDiagonal family.patchMotion current index))
      (referencePointShapeVelocity scales family.patchMotion time index) time at actual
  apply actual.congr_of_eventuallyEq
  filter_upwards [near] with current currentUpper
  exact (pointShapeChart_eq_paper_shape_of_upper family.patchMotion current index currentUpper).symm

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
