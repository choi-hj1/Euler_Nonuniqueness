import EulerNonuniqueness.Section3.PeriodicHilbertModes
import EulerNonuniqueness.General.PeriodicFourierUniqueness

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance : NormedSpace ℂ PeriodicHolderHalf := complexHolderNormedSpace

def integerCircleMode : ℤ → PeriodicHolderHalf
  | .ofNat degree => positiveCircleMode degree
  | .negSucc degree => holderConjugate (positiveCircleMode (degree + 1))

def periodicHilbertMultiplier : ℤ → ℂ
  | .ofNat 0 => 0
  | .ofNat (_ + 1) => -Complex.I
  | .negSucc _ => Complex.I

theorem periodicHilbertCLM_integer_mode (degree : ℤ) :
    periodicHilbertCLM (integerCircleMode degree) =
      periodicHilbertMultiplier degree • integerCircleMode degree := by
  cases degree with
  | ofNat degree =>
    cases degree with
    | zero => simpa only [integerCircleMode, periodicHilbertMultiplier, zero_smul]
        using periodicHilbertCLM_constant_mode
    | succ degree => exact periodicHilbertCLM_positive_mode degree
  | negSucc degree => exact periodicHilbertCLM_negative_mode degree

theorem fourier_one_standardCircle (label : ℝ) :
    fourier 1 (label : AddCircle (2 * Real.pi)) = standardCircle label := by
  rw [fourier_coe_apply]
  unfold standardCircle
  congr 1
  have piNonzero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

theorem positiveCircleMode_fourier (degree : ℕ) (label : ℝ) :
    (positiveCircleMode degree).val.1 label =
      fourier (degree : ℤ) (label : AddCircle (2 * Real.pi)) := by
  induction degree with
  | zero => simp only [positiveCircleMode_value, pow_zero, Int.natCast_zero, fourier_zero]
  | succ degree induction =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ← induction, fourier_one_standardCircle,
      positiveCircleMode_value, positiveCircleMode_value, pow_succ]

theorem integerCircleMode_fourier (degree : ℤ) (label : ℝ) :
    (integerCircleMode degree).val.1 label =
      fourier degree (label : AddCircle (2 * Real.pi)) := by
  cases degree with
  | ofNat degree => exact positiveCircleMode_fourier degree label
  | negSucc degree =>
    change star ((positiveCircleMode (degree + 1)).val.1 label) = _
    rw [positiveCircleMode_fourier]
    simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, Complex.star_def] using
      (fourier_neg (n := (degree + 1 : ℕ)) (x := (label : AddCircle (2 * Real.pi)))).symm

theorem integerCircleMode_zero (degree : ℤ) : (integerCircleMode degree).val.1 0 = 1 := by
  rw [integerCircleMode_fourier]
  exact fourier_eval_zero degree

theorem periodicHilbertMultiplier_sq (degree : ℤ) :
    periodicHilbertMultiplier degree ^ 2 = if degree = 0 then 0 else -1 := by
  cases degree with
  | ofNat degree =>
    cases degree with
    | zero => simp [periodicHilbertMultiplier]
    | succ degree =>
      have nonzero : (degree : ℤ) + 1 ≠ 0 := by omega
      simp [periodicHilbertMultiplier, Complex.I_sq, nonzero]
  | negSucc degree => simp [periodicHilbertMultiplier, Complex.I_sq]

end

end EulerNonuniqueness.Paper
