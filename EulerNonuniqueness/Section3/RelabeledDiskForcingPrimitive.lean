import EulerNonuniqueness.Section3.DiskForcingWeightedPrimitive
import EulerNonuniqueness.Section3.FixedRelabelDerivativeConjugacy

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def c1NaturalPower (data : PeriodicC1HolderHalf) : ℕ → PeriodicC1HolderHalf
  | 0 => c1Constant 1
  | degree + 1 => c1Product data (c1NaturalPower data degree)

theorem c1NaturalPower_value (data : PeriodicC1HolderHalf) (degree : ℕ) (label : ℝ) :
    (c1NaturalPower data degree).val.1 label = data.val.1 label ^ degree := by
  induction degree with
  | zero => rfl
  | succ degree induction =>
    change data.val.1 label * (c1NaturalPower data degree).val.1 label = _
    rw [induction, pow_succ]
    ring

def relabeledDiskForcingMode (angular : PeriodicC1HolderHalf) (degree : ℕ) : PeriodicC1HolderHalf :=
  c1Conjugate (c1NaturalPower (diskRelabelCurve angular 1) (degree + 1))

theorem fixedRelabelEquivalence_forcingMode (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) (degree : ℕ) :
    fixedRelabelEquivalence angular small (c1Conjugate (diskCircleMode (degree + 1))) =
      relabeledDiskForcingMode angular degree := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [fixedRelabelEquivalence_value, c1Conjugate_value, diskCircleMode_value]
  change _ = star ((c1NaturalPower (diskRelabelCurve angular 1) (degree + 1)).val.1 label)
  rw [c1NaturalPower_value]
  have circle := congrArg (fun data : PeriodicC1HolderHalf => data.val.1 label)
    (fixedRelabelEquivalence_circle angular small realValues)
  change (fixedRelabelEquivalence angular small standardCircleBanach).val.1 label =
    (diskRelabelCurve angular 1).val.1 label at circle
  rw [fixedRelabelEquivalence_value] at circle
  change standardCircle (periodicLabelShift angular label) = (diskRelabelCurve angular 1).val.1 label at circle
  rw [circle]

theorem relabeledDiskDerivative_forcing_mode (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (degree : ℕ) (coefficient : ℂ) :
    relabeledDiskDerivative angular (coefficient • relabeledDiskForcingMode angular degree) =
      (-Complex.I / 2 * coefficient) • relabeledDiskForcingMode angular degree := by
  have intertwines := relabeledDiskDerivative_intertwines angular small realValues nearby
  have actual := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
    operator (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) intertwines
  change relabeledDiskDerivative angular
    (fixedRelabelEquivalence angular small (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) =
    fixedRelabelEquivalence angular small
      (diskRotatingDerivative (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) at actual
  rw [diskRotatingDerivative_forcing_mode, fixedRelabelEquivalence_complex_smul,
    fixedRelabelEquivalence_complex_smul, fixedRelabelEquivalence_forcingMode angular small realValues] at actual
  exact actual

def relabeledDiskForcingPrimitive (angular : PeriodicC1HolderHalf) (degree : ℕ)
    (frequency : ℝ) (amplitude : ℝ → ℂ) (time : ℝ) : PeriodicC1HolderHalf :=
  (diskForcingPrimitiveFactor degree frequency * amplitude time * diskForcingPhase degree frequency time) •
    relabeledDiskForcingMode angular degree

theorem fixedRelabelEquivalence_forcingPrimitive (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (degree : ℕ) (frequency : ℝ) (amplitude : ℝ → ℂ) (time : ℝ) :
    fixedRelabelEquivalence angular small (diskForcingPrimitive degree frequency amplitude time) =
      relabeledDiskForcingPrimitive angular degree frequency amplitude time := by
  unfold diskForcingPrimitive relabeledDiskForcingPrimitive
  rw [fixedRelabelEquivalence_complex_smul, fixedRelabelEquivalence_forcingMode angular small realValues]

theorem relabeledDiskForcingPrimitive_weighted_bound (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (degree : ℕ) {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℝ → ℂ) (time : ℝ) :
    ‖relabeledDiskForcingPrimitive angular degree frequency amplitude time‖ ≤
      (32 / |frequency|) * ((2 : ℝ) ^ (degree + 1) * ‖amplitude time‖) := by
  rw [← fixedRelabelEquivalence_forcingPrimitive angular small realValues]
  have composed := fixedRelabelEquivalence_norm_bound angular small
    (diskForcingPrimitive degree frequency amplitude time)
  have primitive := diskForcingPrimitive_weighted_bound degree nonzero amplitude time
  calc
    _ ≤ 8 * ‖diskForcingPrimitive degree frequency amplitude time‖ := composed
    _ ≤ 8 * ((4 / |frequency|) * ((2 : ℝ) ^ (degree + 1) * ‖amplitude time‖)) :=
      mul_le_mul_of_nonneg_left primitive (by norm_num)
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
