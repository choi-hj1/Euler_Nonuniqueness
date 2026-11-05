import EulerNonuniqueness.Section3.HolderFourierAverage

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance hilbertSquareHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance hilbertSquareC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance hilbertSquareHolderModule : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance hilbertSquareHolderComplexSpace : NormedSpace ℂ PeriodicHolderHalf := complexHolderNormedSpace
local instance hilbertSquarePositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem c1ValueHolder_periodicHilbert (data : PeriodicC1HolderHalf) :
    c1ValueHolder (periodicHilbertC1 data) = periodicHilbertCLM (c1ValueHolder data) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem holderFourierAverage_periodicHilbert (data : PeriodicC1HolderHalf) (degree : ℤ) :
    periodicHilbertCLM (holderFourierAverage data degree) =
      holderFourierAverage (periodicHilbertC1 data) degree := by
  unfold holderFourierAverage
  rw [c1ValueHolder_periodicHilbert, periodicHilbertCLM_smul_complex]
  congr 1
  have identity := periodicHilbertCCLM.intervalIntegral_comp_comm
    (holderFourierAverage_integrable data degree)
  change
    (∫ offset in (0 : ℝ)..(2 * Real.pi), periodicHilbertCLM
      (circleFourierReal (-degree) offset • holderLabelShift offset (c1ValueHolder data))) =
      periodicHilbertCLM (∫ offset in (0 : ℝ)..(2 * Real.pi),
        circleFourierReal (-degree) offset • holderLabelShift offset (c1ValueHolder data)) at identity
  rw [← identity]
  apply intervalIntegral.integral_congr
  intro offset _
  dsimp only
  rw [periodicHilbertCLM_smul_complex, periodicHilbertCLM_shift]

theorem periodicHilbertC1_fourierCoeff (data : PeriodicC1HolderHalf) (degree : ℤ) :
    fourierCoeff (periodicContinuousLift (periodicHilbertC1 data).val.1.continuous
      (PeriodicC1HolderHalf.periodic (periodicHilbertC1 data))) degree =
      periodicHilbertMultiplier degree *
        fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree := by
  have identity := holderFourierAverage_periodicHilbert data degree
  rw [holderFourierAverage_eq, holderFourierAverage_eq,
    periodicHilbertCLM_smul_complex, periodicHilbertCLM_integer_mode] at identity
  have evaluated := congrArg (fun density : PeriodicHolderHalf => density.val.1 0) identity
  simp only [complexHolder_smul_value, integerCircleMode_zero, mul_one] at evaluated
  exact evaluated.symm.trans (mul_comm _ _)

theorem periodicHilbertC1_mean_zero (data : PeriodicC1HolderHalf) :
    (∫ label in (0 : ℝ)..(2 * Real.pi), (periodicHilbertC1 data).val.1 label) = 0 := by
  have coefficient := periodicHilbertC1_fourierCoeff data 0
  rw [fourierCoeff_eq_intervalIntegral _ _ 0] at coefficient
  simp only [zero_add, neg_zero, periodicContinuousLift_coe, fourier_zero, one_smul,
    periodicHilbertMultiplier, zero_mul] at coefficient
  exact (smul_eq_zero.mp coefficient).resolve_left (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)

theorem periodicHilbertC1_sq_of_mean_zero (data : PeriodicC1HolderHalf)
    (meanZero : (∫ label in (0 : ℝ)..(2 * Real.pi), data.val.1 label) = 0) :
    periodicHilbertC1 (periodicHilbertC1 data) = -data := by
  have negLift :
      periodicContinuousLift (-data).val.1.continuous (PeriodicC1HolderHalf.periodic (-data)) =
      (-1 : ℂ) • periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data) := by
    apply ContinuousMap.ext
    intro quotient
    induction quotient using QuotientAddGroup.induction_on with
    | H label =>
      simp only [periodicContinuousLift_coe, ContinuousMap.smul_apply, smul_eq_mul, neg_one_mul]
      rfl
  have zeroCoefficient :
      fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) 0 = 0 := by
    rw [fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [zero_add, neg_zero, periodicContinuousLift_coe, fourier_zero, one_smul, meanZero, smul_zero]
  have functionEquality := eq_of_periodic_fourierCoeff_eq
    (periodicHilbertC1 (periodicHilbertC1 data)).val.1.continuous (-data).val.1.continuous
    (PeriodicC1HolderHalf.periodic _) (PeriodicC1HolderHalf.periodic _) (fun degree => by
      rw [periodicHilbertC1_fourierCoeff, periodicHilbertC1_fourierCoeff, negLift]
      change periodicHilbertMultiplier degree * (periodicHilbertMultiplier degree *
        fourierCoeff (periodicContinuousLift data.val.1.continuous
          (PeriodicC1HolderHalf.periodic data)) degree) =
        fourierCoeff (fun quotient => (-1 : ℂ) *
          periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data) quotient) degree
      rw [fourierCoeff.const_mul]
      by_cases zero : degree = 0
      · subst degree
        rw [zeroCoefficient]
        simp
      · calc
          _ = periodicHilbertMultiplier degree ^ 2 *
              fourierCoeff (periodicContinuousLift data.val.1.continuous
                (PeriodicC1HolderHalf.periodic data)) degree := by ring
          _ = _ := by rw [periodicHilbertMultiplier_sq, if_neg zero])
  exact PeriodicC1HolderHalf.ext_value (fun label => congrFun functionEquality label)

end

end EulerNonuniqueness.Paper
