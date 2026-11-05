import EulerNonuniqueness.Section6.FourPointSpeedBound
import EulerNonuniqueness.General.InteriorNormGronwall

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Section6

theorem fourPointField_difference_le {coefficient gap : ℝ} (gapPositive : 0 < gap)
    (first second : FourPointConfiguration)
    (firstSeparated : ∀ target source, source ≠ target → gap ≤ ‖first target - first source‖)
    (secondSeparated : ∀ target source, source ≠ target → gap ≤ ‖second target - second source‖) :
    ‖fourPointField coefficient first - fourPointField coefficient second‖ ≤
      (8 * |coefficient| / gap ^ 2) * ‖first - second‖ := by
  have term (target source : Fin 4) :
      ‖(if source = target then (0 : ℂ) else (fourPointSign source : ℂ) / star (first target - first source)) -
        (if source = target then (0 : ℂ) else (fourPointSign source : ℂ) / star (second target - second source))‖ ≤
        2 * ‖first - second‖ / gap ^ 2 := by
    by_cases same : source = target
    · simp only [if_pos same, sub_self, norm_zero]
      positivity
    · rw [if_neg same, if_neg same, div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, norm_mul]
      have sign : ‖(fourPointSign source : ℂ)‖ = 1 := by
        unfold fourPointSign
        split_ifs <;> norm_num
      rw [sign, one_mul]
      have firstNonzero : star (first target - first source) ≠ 0 :=
        star_ne_zero.mpr (norm_pos_iff.mp (gapPositive.trans_le (firstSeparated target source same)))
      have secondNonzero : star (second target - second source) ≠ 0 :=
        star_ne_zero.mpr (norm_pos_iff.mp (gapPositive.trans_le (secondSeparated target source same)))
      have inverse := dist_inv_inv₀ firstNonzero secondNonzero
      simp only [dist_eq_norm, ← star_sub, norm_star] at inverse
      rw [inverse]
      have difference : (first target - first source) - (second target - second source) =
          (first - second) target - (first - second) source := by simp; abel
      rw [difference]
      have targetBound := norm_le_pi_norm (first - second) target
      have sourceBound := norm_le_pi_norm (first - second) source
      have numerator : ‖(first - second) target - (first - second) source‖ ≤ 2 * ‖first - second‖ :=
        (norm_sub_le _ _).trans (by linarith)
      have denominator : gap ^ 2 ≤ ‖first target - first source‖ * ‖second target - second source‖ := by
        nlinarith only [mul_le_mul (firstSeparated target source same) (secondSeparated target source same)
          gapPositive.le (norm_nonneg (first target - first source))]
      exact div_le_div₀ (by positivity) numerator (by positivity) denominator
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro target
  change ‖fourPointField coefficient first target - fourPointField coefficient second target‖ ≤ _
  unfold fourPointField
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  have triangle := norm_sum_le (Finset.univ : Finset (Fin 4))
    (fun source => (if source = target then (0 : ℂ) else (fourPointSign source : ℂ) / star (first target - first source)) -
      (if source = target then (0 : ℂ) else (fourPointSign source : ℂ) / star (second target - second source)))
  have total := Finset.sum_le_sum (fun source (_ : source ∈ (Finset.univ : Finset (Fin 4))) => term target source)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at total
  exact (mul_le_mul_of_nonneg_left (triangle.trans total) (abs_nonneg coefficient)).trans_eq (by ring)

theorem fourPoint_forced_passage_error
    {actual reference error : ℝ → FourPointConfiguration} {coefficient gap horizon forcing : ℝ}
    (horizonPositive : 0 < horizon) (gapPositive : 0 < gap) (forcingNonnegative : 0 ≤ forcing)
    (actualContinuous : ContinuousOn actual (Icc 0 horizon))
    (referenceContinuous : ContinuousOn reference (Icc 0 horizon))
    (errorContinuous : ContinuousOn error (Icc 0 horizon))
    (actualEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt actual (fourPointField coefficient (actual time) + error time) time)
    (referenceEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt reference (fourPointField coefficient (reference time)) time)
    (actualSeparated : ∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target →
      gap ≤ ‖actual time target - actual time source‖)
    (referenceSeparated : ∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target →
      gap ≤ ‖reference time target - reference time source‖)
    (errorBound : ∀ time ∈ Icc 0 horizon, ‖error time‖ ≤ forcing) :
    ∀ time ∈ Icc 0 horizon, ‖actual time - reference time‖ ≤
      (‖actual 0 - reference 0‖ + forcing * time) * Real.exp ((8 * |coefficient| / gap ^ 2) * time) := by
  have fieldContinuous (path : ℝ → FourPointConfiguration)
      (pathContinuous : ContinuousOn path (Icc 0 horizon))
      (separated : ∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target →
        gap ≤ ‖path time target - path time source‖) :
      ContinuousOn (fun time => fourPointField coefficient (path time)) (Icc 0 horizon) := by
    intro time member
    apply (fourPointField_contDiffAt coefficient (fun target source different =>
      norm_pos_iff.mp (gapPositive.trans_le (separated time member target source different)))).continuousAt.comp_continuousWithinAt
    exact pathContinuous time member
  apply EulerNonuniqueness.General.norm_constant_forcing_gronwall_of_interior_derivative
    horizonPositive (by positivity) forcingNonnegative (actualContinuous.sub referenceContinuous)
    (((fieldContinuous actual actualContinuous actualSeparated).add errorContinuous).sub
      (fieldContinuous reference referenceContinuous referenceSeparated))
    (fun time member => (actualEquation time member).sub (referenceEquation time member))
  intro time member
  have triangle := norm_add_le (fourPointField coefficient (actual time) -
    fourPointField coefficient (reference time)) (error time)
  have identity : fourPointField coefficient (actual time) + error time -
      fourPointField coefficient (reference time) =
      (fourPointField coefficient (actual time) - fourPointField coefficient (reference time)) + error time := by abel
  rw [identity]
  exact triangle.trans (add_le_add (fourPointField_difference_le gapPositive _ _
    (actualSeparated time ⟨member.1.le, member.2.le⟩)
    (referenceSeparated time ⟨member.1.le, member.2.le⟩)) (errorBound time ⟨member.1.le, member.2.le⟩))

end EulerNonuniqueness.Section6
