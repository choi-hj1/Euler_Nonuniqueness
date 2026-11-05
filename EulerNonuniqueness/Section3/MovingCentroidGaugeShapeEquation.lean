import EulerNonuniqueness.Section3.MovingCentroidGaugeMaterial
import EulerNonuniqueness.Section3.MovingCentroidGaugeConservation
import EulerNonuniqueness.Section3.ContourCentroidSelfGauge
import EulerNonuniqueness.Section3.DiskStationaryInverseODE

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingShapeEquationHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingShapeEquationC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def FiniteContourConfiguration.movingStateExternalField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (index : Fin count) :
    PeriodicC1HolderHalf :=
  ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
    (((configuration.movingStatePhase state index)⁻¹ : Circle) : ℂ) •
      extendedCrossContourVelocity (configuration.movingStatePhysicalContour state index)
        (configuration.movingStatePhysicalContour state other)

theorem FiniteContourConfiguration.movingStateRawField_self_external {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (index : Fin count) :
    configuration.movingStateRawField state index =
      configuration.density index • diskEulerRotatingField (state.2.2 index) +
        configuration.movingStateExternalField state index := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (configuration.density index : ℂ) * (extendedContourVelocity (state.2.2 index)).val.1 label +
      (configuration.movingStateExternalField state index).val.1 label -
      ((configuration.density index / 2 : ℝ) : ℂ) * (Complex.I * (state.2.2 index).val.1 label) =
    (configuration.density index : ℂ) * ((extendedContourVelocity (state.2.2 index)).val.1 label -
      (Complex.I / 2) * (state.2.2 index).val.1 label) +
      (configuration.movingStateExternalField state index).val.1 label
  push_cast
  ring

theorem FiniteContourConfiguration.movingStateShapeField_of_centered {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (index : Fin count)
    (small : ‖state.2.2 index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (centered : contourCentroidFunctional (state.2.2 index) = 0) :
    (configuration.movingStateVectorField state).2.2 index =
      configuration.density index • diskEulerRotatingField (state.2.2 index) +
        contourCentroidGaugeProjection (state.2.2 index) (configuration.movingStateExternalField state index) := by
  change contourCentroidGaugeProjection (state.2.2 index) (configuration.movingStateRawField state index) = _
  rw [configuration.movingStateRawField_self_external, map_add]
  congr 1
  have selfIdentity : configuration.density index • diskEulerRotatingField (state.2.2 index) =
      configuration.density index • extendedContourVelocity (state.2.2 index) -
        (configuration.density index / 2) • (Complex.I • state.2.2 index) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (configuration.density index : ℂ) * ((extendedContourVelocity (state.2.2 index)).val.1 label -
      (Complex.I / 2) * (state.2.2 index).val.1 label) =
      (configuration.density index : ℂ) * (extendedContourVelocity (state.2.2 index)).val.1 label -
        ((configuration.density index / 2 : ℝ) : ℂ) * (Complex.I * (state.2.2 index).val.1 label)
    push_cast
    ring
  rw [selfIdentity]
  exact contourCentroidGaugeProjection_rotating_self (state.2.2 index) (configuration.density index) small centered

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem shape_hasDerivAt_self_external
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCentered : ∀ index, contourCentroidFunctional (initial.2.2 index) = 0)
    (marginPositive : 0 < margin) {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (safe : margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count) :
    HasDerivAt (fun current => (trajectory.curve current).2.2 index)
      (configuration.density index • diskEulerRotatingField ((trajectory.curve time).2.2 index) +
        contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
          (configuration.movingStateExternalField (trajectory.curve time) index)) time := by
  have actual := trajectory.shape_component_hasDerivAt inside index
  have centered : contourCentroidFunctional ((trajectory.curve time).2.2 index) = 0 :=
    (trajectory.contourCentroid_conserved inside index).trans (initialCentered index)
  have small : ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)) :=
    ((trajectory.admissible time).2.1 index).trans_lt trajectory.shape_small
  rw [trajectory.velocity_eq_uncut_of_margin marginPositive time safe,
    configuration.movingStateShapeField_of_centered (trajectory.curve time) index small centered] at actual
  exact actual

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
