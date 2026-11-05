import EulerNonuniqueness.Section3.ContourContinuousVectors
import EulerNonuniqueness.Section3.ContourIndependentSymmetry
import EulerNonuniqueness.Section3.HolderFourierAverage
import EulerNonuniqueness.Section3.ContourLocalEvolution

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance continuousFourierC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance continuousFourierPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def contourLabelShiftCCLM (offset : ℝ) : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  standardCircle offset • normalizedContourShiftCCLM offset

theorem contourLabelShiftCCLM_value (offset : ℝ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (contourLabelShiftCCLM offset data).val.1 label = data.val.1 (label + offset) := by
  change standardCircle offset * ((standardCircle offset)⁻¹ * data.val.1 (label + offset)) = _
  rw [← mul_assoc, mul_inv_cancel₀ (by simp [standardCircle, Complex.exp_ne_zero]), one_mul]

theorem continuous_contourLabelShiftCCLM (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    Continuous (fun offset => contourLabelShiftCCLM offset data) := by
  have circleContinuous : Continuous standardCircle := by unfold standardCircle; fun_prop
  have orbit : Continuous (fun offset => normalizedContourShiftCLM offset data) := member
  exact circleContinuous.smul orbit

def contourC1FourierAverage (data : PeriodicC1HolderHalf) (degree : ℤ) : PeriodicC1HolderHalf :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) •
    ∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset • contourLabelShiftCCLM offset data

theorem contourC1FourierAverage_integrable (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) (degree : ℤ) :
    IntervalIntegrable (fun offset => circleFourierReal (-degree) offset • contourLabelShiftCCLM offset data)
      volume 0 (2 * Real.pi) :=
  ((circleFourierReal_continuous (-degree)).smul (continuous_contourLabelShiftCCLM data member)).intervalIntegrable _ _

theorem contourC1FourierAverage_value (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) (degree : ℤ) (target : ℝ) :
    (contourC1FourierAverage data degree).val.1 target =
      fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree *
        (integerCircleMode degree).val.1 target := by
  have evaluation := (contourLabelEvaluation target).intervalIntegral_comp_comm
    (contourC1FourierAverage_integrable data member degree)
  change
    (∫ offset in (0 : ℝ)..(2 * Real.pi),
      (circleFourierReal (-degree) offset • contourLabelShiftCCLM offset data).val.1 target) =
      (∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset •
        contourLabelShiftCCLM offset data).val.1 target at evaluation
  simp only [complexC1Holder_smul_value, contourLabelShiftCCLM_value] at evaluation
  simp only [add_comm target] at evaluation
  change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    (∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset •
      contourLabelShiftCCLM offset data).val.1 target = _
  rw [← evaluation, periodic_fourier_shift_integral (PeriodicC1HolderHalf.periodic data),
    integerCircleMode_fourier, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, periodicContinuousLift_coe, smul_eq_mul, Complex.real_smul]
  unfold circleFourierReal
  ring

theorem contourC1FourierAverage_eq_zero_iff (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) (degree : ℤ) :
    contourC1FourierAverage data degree = 0 ↔
      fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree = 0 := by
  constructor
  · intro zeroAverage
    have value := contourC1FourierAverage_value data member degree 0
    rw [zeroAverage, integerCircleMode_zero, mul_one] at value
    exact value.symm
  · intro zeroCoefficient
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [contourC1FourierAverage_value data member degree label, zeroCoefficient, zero_mul]
    rfl

end

end EulerNonuniqueness.Paper
