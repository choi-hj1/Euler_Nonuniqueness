import EulerNonuniqueness.Section3.PeriodicHilbertFourierModes
import EulerNonuniqueness.Section3.HolderTranslationContinuity

open MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance fourierAverageHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance fourierAverageC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance fourierAverageHolderModule : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance fourierAverageHolderComplexSpace : NormedSpace ℂ PeriodicHolderHalf := complexHolderNormedSpace
local instance fourierAveragePositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def circleFourierReal (degree : ℤ) (label : ℝ) : ℂ :=
  fourier degree (label : AddCircle (2 * Real.pi))

theorem circleFourierReal_continuous (degree : ℤ) : Continuous (circleFourierReal degree) :=
  (fourier degree).continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))

theorem circleFourierReal_periodic (degree : ℤ) :
    Function.Periodic (circleFourierReal degree) (2 * Real.pi) := by
  intro label
  exact congrArg (fourier degree) (AddCircle.coe_add_period (2 * Real.pi) label)

theorem circleFourierReal_add (degree : ℤ) (first second : ℝ) :
    circleFourierReal degree (first + second) =
      circleFourierReal degree first * circleFourierReal degree second := by
  simp only [circleFourierReal, AddCircle.coe_add, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul]

theorem circleFourierReal_mul_neg (degree : ℤ) (label : ℝ) :
    circleFourierReal degree label * circleFourierReal (-degree) label = 1 := by
  rw [circleFourierReal, circleFourierReal, ← fourier_add, add_neg_cancel, fourier_zero]

def holderEvaluationCCLM (label : ℝ) : PeriodicHolderHalf →L[ℂ] ℂ :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf) (F := ℂ)
    { toFun := fun density => density.val.1 label
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun density => by simpa only [one_mul] using PeriodicHolderHalf.value_bound density label)

def holderFourierAverage (data : PeriodicC1HolderHalf) (degree : ℤ) : PeriodicHolderHalf :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) •
    ∫ offset in (0 : ℝ)..(2 * Real.pi),
      circleFourierReal (-degree) offset • holderLabelShift offset (c1ValueHolder data)

theorem holderFourierAverage_integrable (data : PeriodicC1HolderHalf) (degree : ℤ) :
    IntervalIntegrable (fun offset => circleFourierReal (-degree) offset •
      holderLabelShift offset (c1ValueHolder data)) volume 0 (2 * Real.pi) :=
  ((circleFourierReal_continuous (-degree)).smul (continuous_c1ValueHolder_shift data)).intervalIntegrable _ _

theorem periodic_fourier_shift_integral {function : ℝ → ℂ}
    (periodic : Function.Periodic function (2 * Real.pi)) (degree : ℤ) (target : ℝ) :
    (∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset * function (offset + target)) =
      circleFourierReal degree target *
        ∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset * function offset := by
  let integrand := fun offset => circleFourierReal (-degree) offset * function offset
  have integrandPeriodic : Function.Periodic integrand (2 * Real.pi) := by
    intro offset
    dsimp only [integrand]
    rw [circleFourierReal_periodic (-degree) offset, periodic offset]
  have pointwise (offset : ℝ) : circleFourierReal (-degree) offset * function (offset + target) =
      circleFourierReal degree target * integrand (offset + target) := by
    dsimp only [integrand]
    rw [circleFourierReal_add]
    have inverse := circleFourierReal_mul_neg degree target
    calc
      _ = (circleFourierReal degree target * circleFourierReal (-degree) target) *
          (circleFourierReal (-degree) offset * function (offset + target)) := by rw [inverse, one_mul]
      _ = _ := by ring
  simp_rw [pointwise]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  have integralEquality := integrandPeriodic.intervalIntegral_add_eq target 0
  simpa only [zero_add, zero_add, add_comm (2 * Real.pi) target] using
    congrArg (fun value : ℂ => circleFourierReal degree target * value) integralEquality

theorem holderFourierAverage_value (data : PeriodicC1HolderHalf) (degree : ℤ) (target : ℝ) :
    (holderFourierAverage data degree).val.1 target =
      fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree *
        (integerCircleMode degree).val.1 target := by
  have evaluation := (holderEvaluationCCLM target).intervalIntegral_comp_comm
    (holderFourierAverage_integrable data degree)
  change
    (∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset * data.val.1 (target + offset)) =
      (∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset •
        holderLabelShift offset (c1ValueHolder data)).val.1 target at evaluation
  simp only [add_comm target] at evaluation
  change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    (∫ offset in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) offset •
      holderLabelShift offset (c1ValueHolder data)).val.1 target = _
  rw [← evaluation, periodic_fourier_shift_integral (PeriodicC1HolderHalf.periodic data),
    integerCircleMode_fourier, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, periodicContinuousLift_coe, smul_eq_mul, Complex.real_smul]
  unfold circleFourierReal
  ring

theorem holderFourierAverage_eq (data : PeriodicC1HolderHalf) (degree : ℤ) :
    holderFourierAverage data degree =
      fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree •
        integerCircleMode degree := by
  apply PeriodicHolderHalf.ext_value
  exact holderFourierAverage_value data degree

end

end EulerNonuniqueness.Paper
