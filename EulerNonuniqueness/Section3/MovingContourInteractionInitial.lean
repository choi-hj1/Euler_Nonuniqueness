import EulerNonuniqueness.Section3.MovingContourConfinementTube

noncomputable section

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

theorem contourInteraction_initial_circle {count : ℕ} {configuration : FiniteContourConfiguration count}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach) (index : Fin count) :
    trajectory.contourInteraction index 0 = trajectory.movingFamily.canonicalNormalizedInteractionCoordinate index
      0 (configuration.density index) 0 standardCircleBanach := by
  unfold contourInteraction
  generalize trajectory.movingFamily.canonicalNormalizedInteractionCoordinate index = coordinate
  rw [contourAngular, trajectory.spectralCoordinate_initial_circle initialCircles, map_zero,
    trajectory.initial_identity, initialCircles index]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
