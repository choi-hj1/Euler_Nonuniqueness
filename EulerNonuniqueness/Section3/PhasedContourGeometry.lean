import EulerNonuniqueness.Section3.FiniteContourField
import EulerNonuniqueness.Section3.ComplexHolderInstances
import Mathlib.Analysis.Complex.Circle

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance phasedContourGeometryComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph

def rotateContours {count : ℕ} (phase : Fin count → Circle) (data : Fin count → PeriodicC1HolderHalf)
    (index : Fin count) : PeriodicC1HolderHalf := (phase index : ℂ) • data index

theorem rotateContours_component_norm {count : ℕ} (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : ‖rotateContours phase data index‖ = ‖data index‖ := by
  change ‖(phase index : ℂ) • (data index).val‖ = ‖(data index).val‖
  rw [norm_smul (phase index : ℂ) (data index).val, Circle.norm_coe, one_mul]

theorem rotateContours_norm {count : ℕ} (phase : Fin count → Circle) (data : Fin count → PeriodicC1HolderHalf) :
    ‖rotateContours phase data‖ = ‖data‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg data)).mpr
    intro index
    rw [rotateContours_component_norm]
    exact norm_le_pi_norm data index
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (rotateContours phase data))).mpr
    intro index
    rw [← rotateContours_component_norm phase data index]
    exact norm_le_pi_norm (rotateContours phase data) index

theorem rotateContours_sub {count : ℕ} (phase : Fin count → Circle) (first second : Fin count → PeriodicC1HolderHalf) :
    rotateContours phase (first - second) = rotateContours phase first - rotateContours phase second := by
  funext index
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (phase index : ℂ) * ((first index).val.1 label - (second index).val.1 label) =
    (phase index : ℂ) * (first index).val.1 label - (phase index : ℂ) * (second index).val.1 label
  exact mul_sub _ _ _

theorem rotateContours_difference_norm {count : ℕ} (phase : Fin count → Circle)
    (first second : Fin count → PeriodicC1HolderHalf) :
    ‖rotateContours phase first - rotateContours phase second‖ = ‖first - second‖ := by
  rw [← rotateContours_sub, rotateContours_norm]

def FiniteContourConfiguration.phasedPhysicalContour {count : ℕ} (configuration : FiniteContourConfiguration count)
    (phase : Fin count → Circle) (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : PeriodicC1HolderHalf :=
  configuration.physicalContour (rotateContours phase data) index

theorem FiniteContourConfiguration.phasedPhysicalContour_value {count : ℕ} (configuration : FiniteContourConfiguration count)
    (phase : Fin count → Circle) (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) (label : ℝ) :
    (configuration.phasedPhysicalContour phase data index).val.1 label =
      configuration.center index + configuration.radius index • ((phase index : ℂ) * (data index).val.1 label) := rfl

theorem FiniteContourConfiguration.phasedPhysicalContour_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) (bounded : ‖data index‖ ≤ 3) :
    ‖configuration.phasedPhysicalContour phase data index‖ ≤ ‖configuration.center index‖ + 3 * configuration.radius index :=
  configuration.physicalContour_norm_bound _ index (by simpa only [rotateContours_component_norm] using bounded)

theorem FiniteContourConfiguration.phasedPhysicalContour_separated {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (first second : Fin count)
    (firstBounded : ‖data first‖ ≤ 3) (secondBounded : ‖data second‖ ≤ 3) (sourceLabel targetLabel : ℝ) :
    configuration.crossGap first second ≤
      ‖(configuration.phasedPhysicalContour phase data first).val.1 targetLabel -
        (configuration.phasedPhysicalContour phase data second).val.1 sourceLabel‖ :=
  configuration.physicalContour_separated _ first second
    (by simpa only [rotateContours_component_norm] using firstBounded)
    (by simpa only [rotateContours_component_norm] using secondBounded) sourceLabel targetLabel

theorem FiniteContourConfiguration.phased_cross_velocity_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (first second : Fin count → PeriodicC1HolderHalf) (target source : Fin count) (distinct : target ≠ source)
    (firstBounded : ∀ index, ‖first index‖ ≤ 3) (secondBounded : ∀ index, ‖second index‖ ≤ 3) :
    ‖extendedCrossContourVelocity (configuration.phasedPhysicalContour phase first target) (configuration.phasedPhysicalContour phase first source) -
      extendedCrossContourVelocity (configuration.phasedPhysicalContour phase second target) (configuration.phasedPhysicalContour phase second source)‖ ≤
      configuration.crossLipschitzCoefficient target source * ‖first - second‖ := by
  have result := configuration.cross_velocity_parameter_norm_bound (rotateContours phase first) (rotateContours phase second)
    target source distinct (fun index => by simpa only [rotateContours_component_norm] using firstBounded index)
    (fun index => by simpa only [rotateContours_component_norm] using secondBounded index)
  rw [rotateContours_difference_norm] at result
  exact result

end EulerNonuniqueness.Paper
