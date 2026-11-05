import EulerNonuniqueness.Section3.IndependentForcingRadialBlock

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentFourierSelectionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

local instance independentFourierSelectionPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem standardCircle_inv_power_eq_fourier (degree : ℕ) (offset : ℝ) :
    (standardCircle offset)⁻¹ ^ degree = circleFourierReal (-(degree : ℤ)) offset := by
  unfold circleFourierReal
  rw [fourier_neg, ← positiveCircleMode_fourier, positiveCircleMode_value]
  rw [← Complex.star_def, star_pow, standardCircle_star_eq_inv]

theorem independentForcingRadialBlock_angular_fourier (degree : ℕ) (offset : ℝ) (data : PeriodicC1HolderHalf) :
    contourLabelShiftCCLM offset (independentForcingRadialBlock degree data) =
      circleFourierReal (-((degree + 2 : ℕ) : ℤ)) offset •
        independentForcingRadialBlock degree (contourLabelShiftCCLM offset data) := by
  rw [independentForcingRadialBlock_angular, standardCircle_inv_power_eq_fourier]

theorem independentStrainForcing_negative_fourier_zero (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule)
    (positiveInput : ∀ degree : ℤ, degree ≤ 1 →
      fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree = 0)
    (degree : ℤ) (negative : degree < 0) :
    fourierCoeff (periodicContinuousLift (independentForcingRadialBlock 0 data).val.1.continuous
      (PeriodicC1HolderHalf.periodic (independentForcingRadialBlock 0 data))) degree = 0 := by
  apply contourAngularOperator_fourier_zero (independentForcingRadialBlock 0) 2
    (fun offset current => independentForcingRadialBlock_angular_fourier 0 offset current) data member degree
  exact positiveInput (degree + 2) (by omega)

end

end EulerNonuniqueness.Paper
