import EulerNonuniqueness.Section3.C1PowerDifferenceBound
import EulerNonuniqueness.General.QuadraticRemainderDerivative

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance powerFirstJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace

local instance powerFirstJetOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def c1NaturalPowerFirstJet (data : PeriodicC1HolderHalf) : ℕ → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf
  | 0 => 0
  | degree + 1 => (c1ProductCLM data).comp (c1NaturalPowerFirstJet data degree) +
      c1ProductCLM (c1NaturalPower data degree)

theorem c1NaturalPowerFirstJet_succ_apply (data direction : PeriodicC1HolderHalf) (degree : ℕ) :
    c1NaturalPowerFirstJet data (degree + 1) direction =
      c1Product data (c1NaturalPowerFirstJet data degree direction) +
        c1Product (c1NaturalPower data degree) direction := rfl

theorem c1NaturalPowerFirstJet_apply_bound (data direction : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPowerFirstJet data degree direction‖ ≤ degree * (24 : ℝ) ^ degree * ‖direction‖ := by
  induction degree with
  | zero => simp [c1NaturalPowerFirstJet]
  | succ degree induction =>
      rw [c1NaturalPowerFirstJet_succ_apply]
      calc
        _ ≤ ‖c1Product data (c1NaturalPowerFirstJet data degree direction)‖ +
            ‖c1Product (c1NaturalPower data degree) direction‖ := norm_add_le _ _
        _ ≤ 8 * ‖data‖ * ‖c1NaturalPowerFirstJet data degree direction‖ +
            8 * ‖c1NaturalPower data degree‖ * ‖direction‖ :=
          add_le_add (c1Product_norm_bound _ _) (c1Product_norm_bound _ _)
        _ ≤ 8 * 3 * (degree * (24 : ℝ) ^ degree * ‖direction‖) +
            8 * (24 : ℝ) ^ degree * ‖direction‖ :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left bound (by norm_num)) induction
            (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (c1NaturalPower_norm_bound_twentyFour data bound degree) (by norm_num)) (norm_nonneg _))
        _ ≤ (degree + 1 : ℕ) * (24 : ℝ) ^ (degree + 1) * ‖direction‖ := by
          rw [Nat.cast_add, Nat.cast_one, pow_succ]
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 24) degree) (norm_nonneg direction)]

def c1NaturalPowerJetError (first base : PeriodicC1HolderHalf) (degree : ℕ) : PeriodicC1HolderHalf :=
  c1NaturalPower first degree - c1NaturalPower base degree - c1NaturalPowerFirstJet base degree (first - base)

theorem c1NaturalPowerJetError_succ (first base : PeriodicC1HolderHalf) (degree : ℕ) :
    c1NaturalPowerJetError first base (degree + 1) =
      c1Product first (c1NaturalPowerJetError first base degree) +
        c1Product (first - base) (c1NaturalPowerFirstJet base degree (first - base)) := by
  unfold c1NaturalPowerJetError
  rw [c1NaturalPowerFirstJet_succ_apply]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change first.val.1 label * (c1NaturalPower first degree).val.1 label -
      base.val.1 label * (c1NaturalPower base degree).val.1 label -
      (base.val.1 label * (c1NaturalPowerFirstJet base degree (first - base)).val.1 label +
        (c1NaturalPower base degree).val.1 label * (first.val.1 label - base.val.1 label)) =
    first.val.1 label * ((c1NaturalPower first degree).val.1 label -
      (c1NaturalPower base degree).val.1 label - (c1NaturalPowerFirstJet base degree (first - base)).val.1 label) +
      (first.val.1 label - base.val.1 label) * (c1NaturalPowerFirstJet base degree (first - base)).val.1 label
  ring

theorem c1NaturalPowerJetError_norm_bound (first base : PeriodicC1HolderHalf)
    (firstBound : ‖first‖ ≤ 3) (baseBound : ‖base‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPowerJetError first base degree‖ ≤ degree ^ 2 * (24 : ℝ) ^ degree * ‖first - base‖ ^ 2 := by
  induction degree with
  | zero => simp [c1NaturalPowerJetError, c1NaturalPower, c1NaturalPowerFirstJet]
  | succ degree induction =>
      rw [c1NaturalPowerJetError_succ]
      calc
        _ ≤ ‖c1Product first (c1NaturalPowerJetError first base degree)‖ +
            ‖c1Product (first - base) (c1NaturalPowerFirstJet base degree (first - base))‖ := norm_add_le _ _
        _ ≤ 8 * ‖first‖ * ‖c1NaturalPowerJetError first base degree‖ +
            8 * ‖first - base‖ * ‖c1NaturalPowerFirstJet base degree (first - base)‖ :=
          add_le_add (c1Product_norm_bound _ _) (c1Product_norm_bound _ _)
        _ ≤ 8 * 3 * (degree ^ 2 * (24 : ℝ) ^ degree * ‖first - base‖ ^ 2) +
            8 * ‖first - base‖ * (degree * (24 : ℝ) ^ degree * ‖first - base‖) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left firstBound (by norm_num)) induction
            (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left (c1NaturalPowerFirstJet_apply_bound base _ baseBound degree) (by positivity))
        _ ≤ (degree + 1 : ℕ) ^ 2 * (24 : ℝ) ^ (degree + 1) * ‖first - base‖ ^ 2 := by
          rw [Nat.cast_add, Nat.cast_one, pow_succ]
          have coefficient : 24 * (degree : ℝ) ^ 2 + 8 * degree ≤ 24 * ((degree : ℝ) + 1) ^ 2 := by
            have degreeNonnegative : (0 : ℝ) ≤ degree := Nat.cast_nonneg degree
            nlinarith
          have scaled := mul_le_mul_of_nonneg_right coefficient
            (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 24) degree) (sq_nonneg ‖first - base‖))
          convert scaled using 1 <;> ring

theorem hasFDerivAt_c1NaturalPowerFirstJet (base : PeriodicC1HolderHalf)
    (bound : ‖base‖ < 3) (degree : ℕ) :
    HasFDerivAt (fun data => c1NaturalPower data degree) (c1NaturalPowerFirstJet base degree) base := by
  apply EulerNonuniqueness.General.hasFDerivAt_of_eventual_quadratic_remainder
    (fun data => c1NaturalPower data degree) (c1NaturalPowerFirstJet base degree) base
    (constant := (degree : ℝ) ^ 2 * (24 : ℝ) ^ degree) (by positivity)
  have nearby : ∀ᶠ increment : PeriodicC1HolderHalf in 𝓝 0, ‖base + increment‖ < 3 := by
    have continuity : Continuous (fun increment : PeriodicC1HolderHalf => ‖base + increment‖) :=
      (continuous_const.add continuous_id).norm
    exact (continuity.tendsto 0).eventually (eventually_lt_nhds (by simpa only [add_zero] using bound))
  filter_upwards [nearby] with increment small
  have estimate := c1NaturalPowerJetError_norm_bound (base + increment) base small.le bound.le degree
  simpa only [c1NaturalPowerJetError, add_sub_cancel_left] using estimate

end EulerNonuniqueness.Paper
