import EulerNonuniqueness.Section5.CascadeSourcePreparedPair
import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryHistory

noncomputable section

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

set_option synthInstance.maxHeartbeats 100000

local instance actualCommonBoundaryInitialTraceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem commonBoundaryDistance_initial_zero
    {rawCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (label : Fin (count * 4)) (frequency radius : ℝ) :
    prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance label frequency 0 radius
      (prepared.referenceWitness.trajectory.spectralCoordinate label 0) (prepared.trajectory.spectralCoordinate label 0) = 0 := by
  have rawEqual : prepared.referenceWitness.trajectory.spectralCoordinate label 0 = prepared.trajectory.spectralCoordinate label 0 := by
    simp only [MovingCentroidGaugeTrajectory.spectralCoordinate,
      prepared.referenceWitness.trajectory.initial_identity, prepared.trajectory.initial_identity]
    rfl
  with_reducible_and_instances
    simp only [FiniteMovingPatchFamily.canonicalExteriorCommonBoundaryDistance, rawEqual,
      EulerNonuniqueness.General.weightedBoundaryPairDistance, sub_self, norm_zero, mul_zero, add_zero]

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
