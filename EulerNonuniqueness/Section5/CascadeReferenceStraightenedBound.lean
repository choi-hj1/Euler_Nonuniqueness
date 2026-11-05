import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section6.NormalFormForwardBound
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_reference_straightened_bound
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ thresholdMax →
    ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
      |(referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape prepared.reference graph coordinate index time).2| ≤
        constant * referenceConstant *
          ((scales.strain + scales.strain ^ 2) / scales.omega (index.val + 1) +
            (scales.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨radius, radiusPositive, constant, constantOne, forward⟩ :=
    localNormalFormChart_exists_uniform_forward_bound graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨min (radius / 4) (1 / 8), by positivity, constant, constantOne, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path thresholdSmall time inside index
  obtain ⟨unstable, phaseLift, initial, lift, evolution, coarse, sharp⟩ := prepared.referenceSolution
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have coarseBound := coarse.2.1 time referenceInside index
  have rawSmall : |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < radius := by
    have thresholdBound := thresholdSmall.trans (min_le_left _ _)
    linarith [coarseBound.1, coarseBound.2.1]
  have pointBound := forward (unstableShape prepared.reference time index, stableShape prepared.reference time index) rawSmall
  have sharpBound := (sharp.1 1 (by norm_num) le_rfl time
    ⟨inside.1, inside.2.trans path.stopBound⟩ index).1
  have rawBound : |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤
      referenceConstant * ((scales.strain + scales.strain ^ 2) / scales.omega (index.val + 1) +
        (scales.omega (index.val + 1))⁻¹ ^ 5) := by
    simp only [one_mul] at sharpBound
    linarith [abs_nonneg (angularImpulse scales prepared.reference time index /
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) - 1),
      abs_nonneg (diagonalDifference prepared.reference time index / scales.length (index.val + 1) ^ 2 - 1)]
  exact pointBound.trans (by
    simpa only [referenceStraightenedShape, localNormalFormChart, mul_assoc] using
      mul_le_mul_of_nonneg_left rawBound (show 0 ≤ constant by linarith))

end EulerNonuniqueness.Paper
