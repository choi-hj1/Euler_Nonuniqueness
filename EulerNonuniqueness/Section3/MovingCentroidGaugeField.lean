import EulerNonuniqueness.Section3.CentroidGaugeContourField
import EulerNonuniqueness.Section3.RotationPhaseLipschitz
import EulerNonuniqueness.Section3.CrossContourUniformBound

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance movingGaugeFieldHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeFieldC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

abbrev MovingContourState (count : ℕ) :=
  ℝ × (Fin count → ℂ) × (Fin count → PeriodicC1HolderHalf)

def FiniteContourConfiguration.movingStatePhase {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (index : Fin count) : Circle :=
  Circle.exp ((configuration.density index / 2) * state.1)

def FiniteContourConfiguration.movingStatePhysicalContour {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (index : Fin count) :
    PeriodicC1HolderHalf :=
  c1AffineContour (state.2.1 index) (configuration.radius index)
    ((configuration.movingStatePhase state index : ℂ) • state.2.2 index)

def FiniteContourConfiguration.movingStateRawField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (index : Fin count) :
    PeriodicC1HolderHalf :=
  configuration.density index • extendedContourVelocity (state.2.2 index) +
    (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
      (((configuration.movingStatePhase state index)⁻¹ : Circle) : ℂ) •
        extendedCrossContourVelocity (configuration.movingStatePhysicalContour state index)
          (configuration.movingStatePhysicalContour state other)) -
    (configuration.density index / 2) • ((Complex.I : ℂ) • state.2.2 index)

def FiniteContourConfiguration.movingStateVectorField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) : MovingContourState count :=
  (1, (fun index => configuration.radius index • ((configuration.movingStatePhase state index : ℂ) *
      (fderiv ℝ contourCentroidFunctional (state.2.2 index)) (configuration.movingStateRawField state index))),
    fun index => contourCentroidGaugeProjection (state.2.2 index) (configuration.movingStateRawField state index))

def FiniteContourConfiguration.atMovingState {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (separated : ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖state.2.1 first - state.2.1 second‖) :
    FiniteContourConfiguration count where
  center := state.2.1
  radius := configuration.radius
  density := configuration.density
  radius_pos := configuration.radius_pos
  separated := separated

theorem FiniteContourConfiguration.movingStatePhysicalContour_eq {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (separated : ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖state.2.1 first - state.2.1 second‖)
    (index : Fin count) :
    configuration.movingStatePhysicalContour state index =
      (configuration.atMovingState state separated).phasedPhysicalContour
        (configuration.movingStatePhase state) state.2.2 index := rfl

theorem FiniteContourConfiguration.movingStateRawField_eq {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (separated : ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖state.2.1 first - state.2.1 second‖)
    (index : Fin count) :
    configuration.movingStateRawField state index =
      (configuration.atMovingState state separated).centroidGaugeRawField
        (configuration.movingStatePhase state) state.2.2 index := rfl

theorem FiniteContourConfiguration.movingStateVectorField_centroid_zero {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (index : Fin count)
    (small : ‖state.2.2 index - standardCircleBanach‖ < 1 / 3) :
    (fderiv ℝ contourCentroidFunctional (state.2.2 index))
      ((configuration.movingStateVectorField state).2.2 index) = 0 :=
  contourCentroidGaugeProjection_centroid_zero (state.2.2 index) (configuration.movingStateRawField state index) small

theorem FiniteContourConfiguration.movingStateVectorField_physical_velocity {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (separated : ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖state.2.1 first - state.2.1 second‖)
    (index : Fin count) (label : ℝ) :
    (configuration.movingStateVectorField state).2.1 index +
      configuration.radius index • ((configuration.movingStatePhase state index : ℂ) *
        (((Complex.I * (configuration.density index / 2 : ℝ)) * (state.2.2 index).val.1 label) +
          ((configuration.movingStateVectorField state).2.2 index).val.1 label)) =
      configuration.radius index • ((configuration.movingStatePhase state index : ℂ) *
        ((configuration.atMovingState state separated).phasedVectorField
          (configuration.movingStatePhase state) state.2.2 index).val.1 label) :=
  (configuration.atMovingState state separated).centroidGauge_physical_velocity
    (configuration.movingStatePhase state) state.2.2 index label

end EulerNonuniqueness.Paper
