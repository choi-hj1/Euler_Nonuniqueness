import EulerNonuniqueness.Section3.ActualCentroidStrainResonance

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentFullRadialC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

local instance independentFullRadialPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def independentFullRadial : (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf :=
  independentNegativeRadial + (1 / 2 : ℂ) • (c1MultiplierCCLM standardCircleBanach).comp
    (ContinuousLinearMap.snd ℂ PeriodicC1HolderHalf PeriodicC1HolderHalf)

theorem independentFullRadial_value (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) (label : ℝ) :
    (independentFullRadial pair).val.1 label =
      (star (standardCircle label) * pair.1.val.1 label + standardCircle label * pair.2.val.1 label) / 2 := by
  change (1 / 2 : ℂ) * (star (standardCircle label) * pair.1.val.1 label) +
    (1 / 2 : ℂ) * (standardCircle label * pair.2.val.1 label) = _
  ring

theorem independentFullRadial_shift (offset : ℝ) (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourLabelShiftCCLM offset (independentFullRadial pair) =
      independentFullRadial (contourIndependentShift offset pair) := by
  rw [contourIndependentShift_eq_diagonal]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value, independentFullRadial_value, independentFullRadial_value]
  change (star (standardCircle (label + offset)) * pair.1.val.1 (label + offset) +
      standardCircle (label + offset) * pair.2.val.1 (label + offset)) / 2 =
    (star (standardCircle label) * ((standardCircle offset)⁻¹ * pair.1.val.1 (label + offset)) +
      standardCircle label * ((standardCircle offset)^2 *
        ((standardCircle offset)⁻¹ * pair.2.val.1 (label + offset)))) / 2
  rw [standardCircle_add, star_mul, standardCircle_star_eq_inv]
  have nonzero : standardCircle offset ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  field_simp
  <;> ring

def independentForcingFullRadialBlock (degree : ℕ) : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.weightedOperatorBlock independentFullRadial
    (independentForcingLinearCoefficient degree) independentPositiveMaterial

theorem independentForcingFullRadialBlock_angular (degree : ℕ) (offset : ℝ) (data : PeriodicC1HolderHalf) :
    contourLabelShiftCCLM offset (independentForcingFullRadialBlock degree data) =
      circleFourierReal (-((degree + 2 : ℕ) : ℤ)) offset •
        independentForcingFullRadialBlock degree (contourLabelShiftCCLM offset data) := by
  rw [← standardCircle_inv_power_eq_fourier]
  unfold independentForcingFullRadialBlock
  with_reducible
    exact EulerNonuniqueness.General.weightedOperatorBlock_covariance independentFullRadial
      (independentForcingLinearCoefficient degree) independentPositiveMaterial
      (contourLabelShiftCCLM offset) (contourIndependentShift offset)
      ((standardCircle offset)⁻¹ ^ (degree + 2)) (independentFullRadial_shift offset)
      (independentPositiveMaterial_shift offset) (independentForcingLinearCoefficient_angular degree offset) data

theorem independentStrainForcing_full_radial_resonance_zero (data : PeriodicC1HolderHalf)
    (member : periodicHilbertPositiveProjection data ∈ contourContinuousVectorSubmodule)
    (firstMode : periodicC1FourierCoefficient data 1 = 0) :
    periodicHilbertNegativeProjection
      (independentForcingFullRadialBlock 0 (periodicHilbertPositiveProjection data)) = 0 := by
  apply periodicHilbertNegativeProjection_eq_zero_of_negative_coefficients
  intro degree negative
  apply contourAngularOperator_fourier_zero (independentForcingFullRadialBlock 0) 2
    (fun offset current => independentForcingFullRadialBlock_angular 0 offset current)
    (periodicHilbertPositiveProjection data) member degree
  by_cases nonpositive : degree + 2 ≤ 0
  · exact periodicHilbertPositiveProjection_fourier_nonpositive_zero data (degree + 2) nonpositive
  · have one : degree + 2 = 1 := by omega
    rw [one]
    exact (periodicHilbertPositiveProjection_fourier_one data).trans firstMode

def actualCentroidStrainFullRadialBlock : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.weightedOperatorBlock independentFullRadial
    actualCentroidStrainLinearCoefficient independentPositiveMaterial

theorem actualCentroidStrainFullRadialBlock_eq :
    actualCentroidStrainFullRadialBlock = independentForcingFullRadialBlock 0 := by
  unfold actualCentroidStrainFullRadialBlock actualCentroidStrainLinearCoefficient
    independentForcingFullRadialBlock independentForcingLinearCoefficient
  rw [actualIndependentCentroidStrainDerivative_eq]

theorem actualCentroidStrain_full_radial_tangent_resonance_zero (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    periodicHilbertNegativeProjection
      (actualCentroidStrainFullRadialBlock (periodicHilbertPositiveProjection (diskRadialPart direction))) = 0 := by
  rw [actualCentroidStrainFullRadialBlock_eq]
  exact independentStrainForcing_full_radial_resonance_zero _
    (contourContinuousVectorSubmodule_positive_projection _
      (contourContinuousVectorSubmodule_radial direction member))
    (diskRadialPart_fourierCoeff_one_zero_of_centroid_tangent direction centered)

end

end EulerNonuniqueness.Paper
