import EulerNonuniqueness.Section4.MovingReferencePointDerivative
import EulerNonuniqueness.Section4.ReferenceSmallerFaceRadius

noncomputable section

open Set Metric EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_outward_derivative :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
      ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
        {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
        {initial : MovingContourState (count * 4)},
      ∀ (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
        (scales : Scales),
      (∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
      (∀ source, initial.2.2 source = standardCircleBanach) → 0 < margin →
      ∀ {time deformation memory bound : ℝ}, 0 ≤ time → time < forwardHorizon →
      (∀ current ∈ Icc 0 time, margin ≤ infDist (trajectory.curve current)
        (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (index : Fin count), ReferenceCentroidFieldGeometry scales trajectory.movingFamily.patchMotion time index →
      (∀ patch, BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion time index patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
      deformation ≤ bound / scales.omega (index.val + 1) ^ 2 → scales.length (index.val + 1) ≤ 1 → scales.hessian ≤ 1 →
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference trajectory.movingFamily.patchMotion time index →
      diagonalDifference trajectory.movingFamily.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2 →
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
      scales.length (index.val + 1) < momentRadius / (8 * (memory + 1)) →
      0 < (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index /
        positiveHalfDiagonal trajectory.movingFamily.patchMotion time index).im →
      |unstableShape trajectory.movingFamily.patchMotion time index| ≤ radius →
      |stableShape trajectory.movingFamily.patchMotion time index| ≤ radius →
      referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤ scales.omega (index.val + 1) * radius / 16 →
      ∃ velocity : ℝ, HasDerivAt (fun current => (movingReferenceShapeCoordinates scales (trajectory.curve current) index).1) velocity time ∧
        ((movingReferenceShapeCoordinates scales (trajectory.curve time) index).1 = radius → 0 < velocity) ∧
        ((movingReferenceShapeCoordinates scales (trajectory.curve time) index).1 = -radius → velocity < 0) := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, faces⟩ :=
    exists_uniform_computed_reference_faces_all_smaller
  refine ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory scales densityIdentity radiusIdentity initialCircles marginPositive time deformation memory bound timeNonnegative beforeFinal
    safe amplitudePositive frequencyBound ratioBound alphaPositive index geometry control nonnegative small memoryNonnegative boundNonnegative
    deformationBound lengthBound hessianBound differenceLower differenceUpper momentBound lengthSmall upper unstableBound stableBound forcingSmall
  have evolution := trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles marginPositive
    timeNonnegative beforeFinal safe
  have closed : time ∈ Icc 0 time := ⟨timeNonnegative, le_rfl⟩
  have computed := faces radius radiusPositive radiusBound evolution closed amplitudePositive frequencyBound ratioBound alphaPositive
    index geometry control nonnegative small memoryNonnegative boundNonnegative deformationBound lengthBound hessianBound
    differenceLower differenceUpper momentBound lengthSmall upper unstableBound stableBound forcingSmall
  have shapeSmall : |unstableShape trajectory.movingFamily.patchMotion time index| +
      |stableShape trajectory.movingFamily.patchMotion time index| ≤ 1 / 4 := by
    linarith [radiusBound.trans maximumSmall]
  have derivative := trajectory.movingReferenceShapeCoordinates_hasDerivAt_of_prefix_margin scales densityIdentity radiusIdentity
    initialCircles marginPositive timeNonnegative beforeFinal safe index differenceLower upper shapeSmall
  have unstableDerivative := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time derivative
  simp only [ContinuousLinearMap.coe_fst', Function.comp_def] at unstableDerivative
  have chartIdentity := pointShapeChart_eq_paper_shape_of_upper trajectory.movingFamily.patchMotion time index upper
  have coherentSmall : |(pointShapeChart (positiveHalfDiagonal trajectory.movingFamily.patchMotion time index)
      (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal trajectory.movingFamily.patchMotion time index)
      (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index)).2| ≤ 1 / 4 := by
    simpa only [chartIdentity] using shapeSmall
  have imaginaryGap := pointShapeChart_reference_imaginary_gap _ _ coherentSmall upper
  have denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖positiveHalfDiagonal trajectory.movingFamily.patchMotion time index‖ ^ 2 := by
    dsimp only [diagonalDifference] at differenceLower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal trajectory.movingFamily.patchMotion time index‖]
  have inside : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨(neg_neg_of_pos trajectory.backward_positive).trans_le timeNonnegative, beforeFinal⟩
  have agreement := trajectory.movingReferenceShapeCoordinates_eq_paper initialCircles scales inside index denominatorLower
    (show (1 / 16 : ℝ) ≤ _ by linarith)
  have omegaPositive := scales.omega_pos (zero_lt_one.trans_le frequencyBound) (by linarith : 0 < scales.ratio) (index.val + 1)
  have speedPositive : 0 < scales.omega (index.val + 1) * radius / 2 := by positivity
  refine ⟨(referencePointShapeVelocity scales trajectory.movingFamily.patchMotion time index).1, unstableDerivative, ?_, ?_⟩
  · intro onFace
    have actualFace : unstableShape trajectory.movingFamily.patchMotion time index = radius := by simpa only [agreement] using onFace
    exact speedPositive.trans_le (computed.1 actualFace)
  · intro onFace
    have actualFace : unstableShape trajectory.movingFamily.patchMotion time index = -radius := by simpa only [agreement] using onFace
    exact (computed.2.1 actualFace).trans_lt (neg_neg_of_pos speedPositive)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
