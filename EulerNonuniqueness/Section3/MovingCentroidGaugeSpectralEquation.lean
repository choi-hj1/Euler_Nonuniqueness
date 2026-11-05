import EulerNonuniqueness.Section3.DiskPhysicalSpectralEquation
import EulerNonuniqueness.Section3.MovingCentroidGaugeShapeEquation

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance movingSpectralEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState count}

def spectralCoordinate
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) : PeriodicC1HolderHalf :=
  diskPhysicalSpectralCoordinate ((trajectory.curve time).2.2 index)

def spectralForcing
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) : PeriodicC1HolderHalf :=
  diskPhysicalSpectralInverseDerivative ((trajectory.curve time).2.2 index)
    (contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
      (configuration.movingStateExternalField (trajectory.curve time) index))

theorem spectralCoordinate_initial_circle
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (index : Fin count) : trajectory.spectralCoordinate index 0 = 0 := by
  unfold spectralCoordinate
  rw [trajectory.initial_identity, initialCircles index, diskPhysicalSpectralCoordinate_circle]

end MovingCentroidGaugeTrajectory

theorem MovingCentroidGaugeTrajectory.exists_uniform_spectral_equation_radius :
    ∃ radius > 0, ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState count}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
      (∀ index, initial.2.2 index = standardCircleBanach) → 0 < margin →
      ∀ time : ℝ, time ∈ Ioo (-backwardHorizon) forwardHorizon →
      margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ →
      ∀ index : Fin count, ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < radius →
      HasDerivAt (trajectory.spectralCoordinate index)
        (configuration.density index • diskSpectralTubularEulerField (trajectory.spectralCoordinate index time) +
          trajectory.spectralForcing index time) time := by
  obtain ⟨radius, positive, valid⟩ := diskPhysicalSpectralCoordinate_exists_ODE_radius
  refine ⟨radius, positive, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory initialCircles marginPositive time inside safe index small
  have centered : ∀ label, contourCentroidFunctional (initial.2.2 label) = 0 := by
    intro label
    rw [initialCircles label]
    exact contourCentroidFunctional_standardCircle_zero
  have equation := trajectory.shape_hasDerivAt_self_external centered marginPositive inside safe index
  unfold MovingCentroidGaugeTrajectory.spectralCoordinate MovingCentroidGaugeTrajectory.spectralForcing
  with_reducible
    exact valid (fun current => (trajectory.curve current).2.2 index) time
      (configuration.density index)
      (contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
        (configuration.movingStateExternalField (trajectory.curve time) index)) small equation

end EulerNonuniqueness.Paper
