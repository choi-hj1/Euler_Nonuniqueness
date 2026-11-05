import EulerNonuniqueness.Section3.MovingCanonicalExteriorForcing
import EulerNonuniqueness.Section3.MovingCentroidGaugeShapeEquation
import EulerNonuniqueness.Section3.CanonicalProjectedExteriorSeries

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance movingCanonicalShapeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem shape_hasDerivAt_canonical_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0)
    (initialCentered : ∀ index, contourCentroidFunctional (initial.2.2 index) = 0)
    (marginPositive : 0 < margin) {horizon time distance : ℝ}
    (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (nonnegativeTime : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) (index : Fin count)
    (positive : 0 < distance) (small : 8 * (trajectory.movingFamily.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
      distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖) :
    HasDerivAt (fun current => (trajectory.curve current).2.2 index)
      (configuration.density index • diskEulerRotatingField ((trajectory.curve time).2.2 index) +
        trajectory.movingFamily.canonicalProjectedExteriorContourField index time distance positive small separated
          (Circle.exp (configuration.density index * time / 2)) ((trajectory.curve time).2.2 index)) time := by
  have actual := trajectory.shape_hasDerivAt_self_external initialCentered marginPositive inside (safe time nonnegativeTime) index
  have bound : ‖(trajectory.curve time).2.2 index‖ ≤ 3 :=
    configuration.movingStateAdmissible_shapes_bounded
      ((trajectory.shape_small.trans_le (min_le_left _ _)).le.trans (by norm_num)) (trajectory.admissible time) index
  rw [trajectory.movingStateExternalField_eq_canonical_of_margin initialClock marginPositive
    inside nonnegativeTime safe index positive small separated] at actual
  simpa only [FiniteMovingPatchFamily.canonicalProjectedExteriorContourField, dif_pos bound] using actual

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
