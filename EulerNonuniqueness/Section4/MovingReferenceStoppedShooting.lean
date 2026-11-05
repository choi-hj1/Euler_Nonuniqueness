import EulerNonuniqueness.Section4.MovingReferenceOutwardDerivative
import EulerNonuniqueness.General.CoordinateShootingWithin

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_stopped_shooting :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
      ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
        {centerBound shapeRadius gap margin backwardHorizon forwardHorizon horizon : ℝ},
      ∀ (scales : Scales)
        (initial : closedBall (0 : Fin count → ℝ) radius → MovingContourState (count * 4))
        (trajectories : ∀ parameter, MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
          backwardHorizon forwardHorizon (initial parameter)),
      (∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
      (∀ parameter source, (initial parameter).2.2 source = standardCircleBanach) →
      0 < margin → 0 ≤ horizon → horizon < forwardHorizon →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      Continuous (fun point : closedBall (0 : Fin count → ℝ) radius × ℝ => (trajectories point.1).curve point.2) →
      (∀ parameter index, (movingReferenceShapeCoordinates scales ((trajectories parameter).curve 0) index).1 = parameter.val index) →
      ∀ (memory bound : ℝ), 0 ≤ memory → 0 ≤ bound → scales.hessian ≤ 1 →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ 1) →
      (∀ index : Fin count, scales.length (index.val + 1) < momentRadius / (8 * (memory + 1))) →
      (∀ index : Fin count, referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
        scales.omega (index.val + 1) * radius / 16) →
      ∀ (deformation : closedBall (0 : Fin count → ℝ) radius → ℝ → Fin count → ℝ),
      (∀ parameter time, time ∈ Icc 0 horizon →
        (∀ current ∈ Icc 0 time, ∀ index,
          |(movingReferenceShapeCoordinates scales ((trajectories parameter).curve current) index).1| ≤ radius) →
        (∀ current ∈ Icc 0 time, margin ≤ infDist ((trajectories parameter).curve current)
          (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) ∧
        ∀ index : Fin count,
          ReferenceCentroidFieldGeometry scales (trajectories parameter).movingFamily.patchMotion time index ∧
          (∀ patch, BoundaryCloseToCircle scales (trajectories parameter).movingFamily.patchMotion time index patch
            (deformation parameter time index)) ∧
          0 ≤ deformation parameter time index ∧ deformation parameter time index ≤ 1 / 16 ∧
          deformation parameter time index ≤ bound / scales.omega (index.val + 1) ^ 2 ∧
          scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference (trajectories parameter).movingFamily.patchMotion time index ∧
          diagonalDifference (trajectories parameter).movingFamily.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2 ∧
          ‖centroidAsymmetry (trajectories parameter).movingFamily.patchMotion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 ∧
          0 < (negativeHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index /
            positiveHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index).im ∧
          |unstableShape (trajectories parameter).movingFamily.patchMotion time index| +
            |stableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ 1 / 4 ∧
          |stableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ radius) →
      ∃ parameter, FinitePatchEvolution scales (trajectories parameter).movingFamily.patchMotion horizon ∧
        ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
          |unstableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ radius ∧
          |stableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ radius := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, outward⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_actual_reference_outward_derivative
  refine ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon horizon
    scales initial trajectories densityIdentity radiusIdentity initialCircles marginPositive horizonNonnegative beforeFinal
    amplitudePositive frequencyBound ratioBound alphaPositive jointContinuous initialCoordinate memory bound memoryNonnegative boundNonnegative
    hessianBound lengthBound lengthSmall forcingSmall deformation physical
  let curve : closedBall (0 : Fin count → ℝ) radius → ℝ → Fin count → ℝ := fun parameter time index =>
    (movingReferenceShapeCoordinates scales ((trajectories parameter).curve time) index).1
  have agreement (parameter : closedBall (0 : Fin count → ℝ) radius) (time : ℝ) (closed : time ∈ Icc 0 horizon)
      (prefixBound : ∀ current ∈ Icc 0 time, ∀ index, |curve parameter current index| ≤ radius) (index : Fin count) :
      movingReferenceShapeCoordinates scales ((trajectories parameter).curve time) index =
        (unstableShape (trajectories parameter).movingFamily.patchMotion time index,
          stableShape (trajectories parameter).movingFamily.patchMotion time index) := by
    obtain ⟨safe, conditions⟩ := physical parameter time closed prefixBound
    obtain ⟨geometry, control, nonnegative, small, deformationBound, differenceLower, differenceUpper, momentBound,
      upper, chartSmall, stableBound⟩ := conditions index
    have inside : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
      ⟨(neg_neg_of_pos (trajectories parameter).backward_positive).trans_le closed.1, closed.2.trans_lt beforeFinal⟩
    have denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤
        ‖positiveHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index‖ ^ 2 := by
      dsimp only [diagonalDifference] at differenceLower
      nlinarith [sq_nonneg ‖negativeHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index‖]
    have chartIdentity := pointShapeChart_eq_paper_shape_of_upper (trajectories parameter).movingFamily.patchMotion time index upper
    have coherentSmall : |(Section6.pointShapeChart (positiveHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index)
        (negativeHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index)).1| +
        |(Section6.pointShapeChart (positiveHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index)
        (negativeHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index)).2| ≤ 1 / 4 := by
      simpa only [chartIdentity] using chartSmall
    have imaginaryGap := Section6.pointShapeChart_reference_imaginary_gap _ _ coherentSmall upper
    exact (trajectories parameter).movingReferenceShapeCoordinates_eq_paper (initialCircles parameter) scales inside index
      denominatorLower (by linarith)
  have curveContinuous : Continuous (fun point : closedBall (0 : Fin count → ℝ) radius × ℝ => curve point.1 point.2) := by
    apply continuous_pi
    intro index
    exact ((movingReferenceShapeCoordinates_continuous scales index).comp jointContinuous).fst
  have initialCurve : ∀ parameter, curve parameter 0 = parameter := by
    intro parameter
    funext index
    exact initialCoordinate parameter index
  obtain ⟨parameter, confined⟩ := exists_confined_coordinates_of_outward_derivativeWithin radiusPositive curveContinuous initialCurve (by
    intro parameter time timeInside prefixBound index
    have closed : time ∈ Icc 0 horizon := ⟨timeInside.1, timeInside.2.le⟩
    obtain ⟨safe, conditions⟩ := physical parameter time closed prefixBound
    obtain ⟨geometry, control, nonnegative, small, deformationBound, differenceLower, differenceUpper, momentBound,
      upper, chartSmall, stableBound⟩ := conditions index
    have unstableBound : |unstableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ radius := by
      have coordinateBound := prefixBound time ⟨timeInside.1, le_rfl⟩ index
      simpa only [curve, agreement parameter time closed prefixBound index] using coordinateBound
    obtain ⟨velocity, derivative, positiveFace, negativeFace⟩ := outward radius radiusPositive radiusBound (trajectories parameter) scales
      densityIdentity radiusIdentity (initialCircles parameter) marginPositive timeInside.1 (timeInside.2.trans beforeFinal) safe
      amplitudePositive frequencyBound ratioBound alphaPositive index geometry control nonnegative small memoryNonnegative boundNonnegative
      deformationBound (lengthBound index) hessianBound differenceLower differenceUpper momentBound (lengthSmall index) upper
      unstableBound stableBound (forcingSmall index)
    exact ⟨velocity, derivative.hasDerivWithinAt, positiveFace, negativeFace⟩)
  have everyPrefix (time : ℝ) (closed : time ∈ Icc 0 horizon) :
      ∀ current ∈ Icc 0 time, ∀ index, |curve parameter current index| ≤ radius := by
    intro current currentInside index
    exact confined current ⟨currentInside.1, currentInside.2.trans closed.2⟩ index
  have safe := (physical parameter horizon ⟨horizonNonnegative, le_rfl⟩ (everyPrefix horizon ⟨horizonNonnegative, le_rfl⟩)).1
  refine ⟨parameter, (trajectories parameter).finitePatchEvolution_of_margin scales densityIdentity radiusIdentity (initialCircles parameter)
    marginPositive horizonNonnegative beforeFinal safe, ?_⟩
  intro time closed index
  have prefixBound := everyPrefix time closed
  have coordinateBound := confined time closed index
  have actualBound : |unstableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ radius := by
    simpa only [curve, agreement parameter time closed prefixBound index] using coordinateBound
  exact ⟨actualBound, ((physical parameter time closed prefixBound).2 index).2.2.2.2.2.2.2.2.2.2⟩

end EulerNonuniqueness.Paper
