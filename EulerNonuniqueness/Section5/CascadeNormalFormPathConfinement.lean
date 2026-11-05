import EulerNonuniqueness.Section6.NormalFormChartPathConfinement
import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_normalForm_path_confinement
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ chartRadius > (0 : ℝ),
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ finish : ℝ,
    finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, 0 < (negativeHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index /
      positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index).im) →
    |unstableShape prepared.trajectory.movingFamily.patchMotion 0 index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion 0 index| < radius →
    (∀ time ∈ Icc 0 finish,
      |coordinate (unstableShape prepared.trajectory.movingFamily.patchMotion time index)| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index -
        graph (unstableShape prepared.trajectory.movingFamily.patchMotion time index)| ≤ chartRadius) →
    ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| < radius := by
  obtain ⟨radius, radiusPositive, chartRadius, chartRadiusPositive, confined⟩ :=
    localNormalFormChart_exists_continuous_path_confinement graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨radius, radiusPositive, chartRadius, chartRadiusPositive, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path index finish finishBound upper initial small
  apply confined (fun time => (unstableShape prepared.trajectory.movingFamily.patchMotion time index,
    stableShape prepared.trajectory.movingFamily.patchMotion time index)) finish ?_ initial small
  intro time member
  have nonzero : positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index ≠ 0 := by
    intro zero
    have positive := upper time member
    simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using positive
  exact (prepared.trajectory.movingFamily.centroid_paper_shape_contDiffAt_of_upper index
    (by
      intro patch
      change time ∈ Ioo (-(1 : ℝ)) 3
      exact ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩)
    nonzero (upper time member)).continuousAt.continuousWithinAt

end EulerNonuniqueness.Paper
