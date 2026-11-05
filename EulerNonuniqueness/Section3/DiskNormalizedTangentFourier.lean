import EulerNonuniqueness.Section3.ContourCentroidCircleRadial
import EulerNonuniqueness.Section3.HolderFourierAverage

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance normalizedTangentHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance normalizedTangentC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance normalizedTangentPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem diskRadialPart_fourierCoeff_neg_one_zero_of_centroid_tangent
    (direction : PeriodicC1HolderHalf)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    fourierCoeff (periodicContinuousLift (diskRadialPart direction).val.1.continuous
      (PeriodicC1HolderHalf.periodic (diskRadialPart direction))) (-1) = 0 := by
  rw [fourierCoeff_eq_intervalIntegral _ (-1) (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  simp only [neg_neg, fourier_one_standardCircle, periodicContinuousLift_coe, smul_eq_mul]
  rw [diskRadialPart_first_moment_zero_of_centroid_tangent direction centered, smul_zero]

theorem diskRadialPart_fourierCoeff_one_zero_of_centroid_tangent
    (direction : PeriodicC1HolderHalf)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    fourierCoeff (periodicContinuousLift (diskRadialPart direction).val.1.continuous
      (PeriodicC1HolderHalf.periodic (diskRadialPart direction))) 1 = 0 := by
  have momentZero := diskRadialPart_first_moment_zero_of_centroid_tangent direction centered
  have circleContinuous : Continuous standardCircle := standardCircleBanach.val.1.continuous
  have conjugateIntegral := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm
    ((circleContinuous.mul (diskRadialPart direction).val.1.continuous).intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
  have conjugateZero : (∫ label in (-Real.pi)..Real.pi,
      star (standardCircle label) * (diskRadialPart direction).val.1 label) = 0 := by
    have integrand : (fun label => (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (standardCircle label * (diskRadialPart direction).val.1 label)) =
        fun label => star (standardCircle label) * (diskRadialPart direction).val.1 label := by
      funext label
      change star (standardCircle label * (diskRadialPart direction).val.1 label) = _
      rw [star_mul, diskRadialPart_real]
      ring
    rw [integrand, momentZero] at conjugateIntegral
    simpa only [map_zero] using conjugateIntegral
  rw [fourierCoeff_eq_intervalIntegral _ 1 (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  have mode : ∀ label : ℝ, fourier (-1) (label : AddCircle (2 * Real.pi)) = star (standardCircle label) := by
    intro label
    rw [fourier_neg, fourier_one_standardCircle, Complex.star_def]
  simp only [mode, periodicContinuousLift_coe, smul_eq_mul]
  rw [conjugateZero, smul_zero]

theorem diskRadialPart_fourierCoeff_zero_of_area_tangent
    (direction : PeriodicC1HolderHalf)
    (areaTangent : (fderiv ℝ contourAreaFunctional standardCircleBanach) direction = 0) :
    fourierCoeff (periodicContinuousLift (diskRadialPart direction).val.1.continuous
      (PeriodicC1HolderHalf.periodic (diskRadialPart direction))) 0 = 0 := by
  have radialMeanZero : diskRadialMean direction = 0 := by
    have derivativeIdentity : fderiv ℝ contourAreaFunctional standardCircleBanach =
        (2 * Real.pi) • diskRadialMeanCLM := by
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ)
        hasFDerivAt_contourAreaFunctional_circle
    rw [derivativeIdentity, ContinuousLinearMap.smul_apply, diskRadialMeanCLM_apply] at areaTangent
    change (2 * Real.pi) * diskRadialMean direction = 0 at areaTangent
    exact (mul_eq_zero.mp areaTangent).resolve_left (by positivity)
  rw [fourierCoeff_eq_intervalIntegral _ 0 (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  simp only [neg_zero, fourier_zero, one_smul, periodicContinuousLift_coe]
  have projection := congrArg (fun data : PeriodicC1HolderHalf => data.val.1 0)
    (periodicMeanProjection_diskRadialPart direction)
  dsimp only at projection
  rw [periodicMeanProjectionCCLM_value] at projection
  have shifted := (PeriodicC1HolderHalf.periodic (diskRadialPart direction)).intervalIntegral_add_eq (-Real.pi) 0
  have window : (∫ label in (-Real.pi)..Real.pi, (diskRadialPart direction).val.1 label) =
      ∫ label in (0 : ℝ)..(2 * Real.pi), (diskRadialPart direction).val.1 label := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] using shifted
  rw [window]
  change _ = 0
  have integralZero : (∫ label in (0 : ℝ)..(2 * Real.pi), (diskRadialPart direction).val.1 label) = 0 := by
    change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ label in (0 : ℝ)..(2 * Real.pi), (diskRadialPart direction).val.1 label) = (diskRadialMean direction : ℂ) at projection
    rw [radialMeanZero, Complex.ofReal_zero] at projection
    exact (mul_eq_zero.mp projection).resolve_left (by
      exact_mod_cast (one_div_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0)))
  rw [integralZero, smul_zero]

end EulerNonuniqueness.Paper
