import EulerNonuniqueness.Section3.ContourCentroidGaugeRegularity
import EulerNonuniqueness.Section3.PhasedContourMaterial

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidFieldHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance centroidFieldC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def FiniteContourConfiguration.centroidGaugeRawField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : PeriodicC1HolderHalf :=
  configuration.phasedVectorField phase data index -
    (configuration.density index / 2) • ((Complex.I : ℂ) • data index)

def FiniteContourConfiguration.centroidGaugeShapeField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : PeriodicC1HolderHalf :=
  contourCentroidGaugeProjection (data index) (configuration.centroidGaugeRawField phase data index)

def FiniteContourConfiguration.centroidGaugeCenterField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : ℂ :=
  configuration.radius index • ((phase index : ℂ) *
    (fderiv ℝ contourCentroidFunctional (data index)) (configuration.centroidGaugeRawField phase data index))

theorem FiniteContourConfiguration.centroidGaugeShapeField_centroid_derivative_zero {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count)
    (small : ‖data index - standardCircleBanach‖ < 1 / 3) :
    (fderiv ℝ contourCentroidFunctional (data index)) (configuration.centroidGaugeShapeField phase data index) = 0 :=
  contourCentroidGaugeProjection_centroid_zero (data index) (configuration.centroidGaugeRawField phase data index) small

theorem FiniteContourConfiguration.centroidGauge_physical_velocity {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) (label : ℝ) :
    configuration.centroidGaugeCenterField phase data index +
      configuration.radius index • ((phase index : ℂ) *
        (((Complex.I * (configuration.density index / 2 : ℝ)) * (data index).val.1 label) +
          (configuration.centroidGaugeShapeField phase data index).val.1 label)) =
      configuration.radius index • ((phase index : ℂ) *
        (configuration.phasedVectorField phase data index).val.1 label) := by
  change configuration.radius index • ((phase index : ℂ) *
      (fderiv ℝ contourCentroidFunctional (data index)) (configuration.centroidGaugeRawField phase data index)) +
    configuration.radius index • ((phase index : ℂ) *
      (((Complex.I * (configuration.density index / 2 : ℝ)) * (data index).val.1 label) +
        ((configuration.centroidGaugeRawField phase data index).val.1 label -
          (fderiv ℝ contourCentroidFunctional (data index)) (configuration.centroidGaugeRawField phase data index)))) = _
  change _ = configuration.radius index • ((phase index : ℂ) *
    (configuration.phasedVectorField phase data index).val.1 label)
  have rawIdentity : (configuration.centroidGaugeRawField phase data index).val.1 label =
      (configuration.phasedVectorField phase data index).val.1 label -
        (configuration.density index / 2) • (Complex.I * (data index).val.1 label) := rfl
  rw [rawIdentity]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem FiniteContourConfiguration.centroidGauge_physical_velocity_eq_contour_sum {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf)
    (nearby : ∀ index, ‖data index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (bounded : ∀ index, ‖data index‖ ≤ 3) (index : Fin count) (label : ℝ) :
    configuration.centroidGaugeCenterField phase data index +
      configuration.radius index • ((phase index : ℂ) *
        (((Complex.I * (configuration.density index / 2 : ℝ)) * (data index).val.1 label) +
          (configuration.centroidGaugeShapeField phase data index).val.1 label)) =
      configuration.density index • pointContourVelocity (configuration.phasedPhysicalContour phase data index).val.1
        (configuration.phasedPhysicalContour phase data index).val.2.val.1
        ((configuration.phasedPhysicalContour phase data index).val.1 label) (-Real.pi) Real.pi +
      ∑ other ∈ Finset.univ.erase index, configuration.density other •
        pointContourVelocity (configuration.phasedPhysicalContour phase data other).val.1
          (configuration.phasedPhysicalContour phase data other).val.2.val.1
          ((configuration.phasedPhysicalContour phase data index).val.1 label) (-Real.pi) Real.pi := by
  rw [configuration.centroidGauge_physical_velocity phase data index label]
  exact configuration.phased_physical_vectorField_label_value phase data nearby bounded index label

end EulerNonuniqueness.Paper
