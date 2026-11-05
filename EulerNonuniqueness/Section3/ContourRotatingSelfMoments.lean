import EulerNonuniqueness.Section3.ContourAreaSelfInvariance
import EulerNonuniqueness.Section3.ContourCentroidSelfGauge
import EulerNonuniqueness.Section3.ContourAreaCentroidNormalization
import EulerNonuniqueness.Section3.ContourVelocityTranslationDerivative
import EulerNonuniqueness.Section3.ContourVelocityScaling

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance rotatingSelfMomentsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem rotatingSelfMoments_field_eq_real_combination (data : PeriodicC1HolderHalf) :
    diskEulerRotatingField data = extendedContourVelocity data - (1 / 2 : ℝ) • (Complex.I • data) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (extendedContourVelocity data).val.1 label - (Complex.I / 2) * data.val.1 label =
    (extendedContourVelocity data).val.1 label - (1 / 2 : ℝ) • (Complex.I * data.val.1 label)
  rw [Complex.real_smul]
  push_cast
  ring

theorem contourAreaFunctional_derivative_rotating_self (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    fderiv ℝ contourAreaFunctional data (diskEulerRotatingField data) = 0 := by
  rw [rotatingSelfMoments_field_eq_real_combination, map_sub, map_smul,
    contourAreaFunctional_derivative_self data small, contourAreaFunctional_derivative_rotation,
    smul_zero, sub_zero]

theorem contourCentroidFunctional_derivative_raw_rotating_self (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    fderiv ℝ contourCentroidFunctional data (diskEulerRotatingField data) =
      -(1 / 2 : ℝ) • (Complex.I * contourCentroidFunctional data) := by
  rw [rotatingSelfMoments_field_eq_real_combination]
  simpa only [one_smul] using contourCentroidFunctional_derivative_rotating_self data 1 small

theorem diskEulerRotatingField_real_smul (data : PeriodicC1HolderHalf) (scalar : ℝ) (nonzero : scalar ≠ 0)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (scaledSmall : ‖scalar • data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    diskEulerRotatingField (scalar • data) = scalar • diskEulerRotatingField data := by
  have scalarIdentity : (scalar : ℂ) • data = scalar • data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (scalar : ℂ) * data.val.1 label = scalar • data.val.1 label
    rw [Complex.real_smul]
  have velocity := extendedContourVelocity_scale data (scalar : ℂ) (Complex.ofReal_ne_zero.mpr nonzero)
    small (by simpa only [scalarIdentity] using scaledSmall)
  rw [scalarIdentity] at velocity
  apply PeriodicC1HolderHalf.ext_value
  intro label
  have atLabel := congrArg (fun current : PeriodicC1HolderHalf => current.val.1 label) velocity
  change (extendedContourVelocity (scalar • data)).val.1 label =
    (scalar : ℂ) * (extendedContourVelocity data).val.1 label at atLabel
  change (extendedContourVelocity (scalar • data)).val.1 label - (Complex.I / 2) *
    ((scalar : ℂ) * data.val.1 label) = scalar •
      ((extendedContourVelocity data).val.1 label - (Complex.I / 2) * data.val.1 label)
  rw [atLabel, Complex.real_smul]
  ring

theorem diskEulerRotatingField_recenter (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (centeredSmall : ‖contourCentroidRecenter data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    diskEulerRotatingField (contourCentroidRecenter data) = diskEulerRotatingField data -
      c1ConstantCLM (fderiv ℝ contourCentroidFunctional data (diskEulerRotatingField data)) := by
  have translatedSmall : ‖data + c1Constant (-contourCentroidFunctional data) - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi)) := by
    change ‖data + c1ConstantCLM (-contourCentroidFunctional data) - standardCircleBanach‖ < _
    simpa only [contourCentroidRecenter, map_neg, sub_eq_add_neg] using centeredSmall
  have originalSmall : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    lt_min (lt_of_lt_of_le (small.trans_le (min_le_left _ _)) (by norm_num)) (small.trans_le (min_le_right _ _))
  have velocity := extendedContourVelocity_translate data (-contourCentroidFunctional data) originalSmall translatedSmall
  change extendedContourVelocity (data + c1ConstantCLM (-contourCentroidFunctional data)) = _ at velocity
  have recenteredVelocity : extendedContourVelocity (contourCentroidRecenter data) = extendedContourVelocity data := by
    simpa only [contourCentroidRecenter, map_neg, sub_eq_add_neg] using velocity
  rw [contourCentroidFunctional_derivative_raw_rotating_self data small]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  have atLabel := congrArg (fun current : PeriodicC1HolderHalf => current.val.1 label) recenteredVelocity
  dsimp only at atLabel
  change (extendedContourVelocity (contourCentroidRecenter data)).val.1 label -
      (Complex.I / 2) * (data.val.1 label - contourCentroidFunctional data) =
    ((extendedContourVelocity data).val.1 label - (Complex.I / 2) * data.val.1 label) -
      (-(1 / 2 : ℝ)) • (Complex.I * contourCentroidFunctional data)
  rw [atLabel, Complex.real_smul]
  push_cast
  ring

end EulerNonuniqueness.Paper
