import EulerNonuniqueness.Section6.SeparatingMomentDerivative

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem inverse_conjugate_fourth_phase {position : ℂ} (nonzero : position ≠ 0) :
    1 / star position ^ 4 =
      Complex.exp (4 * Complex.I * (Complex.arg position : ℂ)) / ((‖position‖ : ℝ) : ℂ) ^ 4 := by
  have normNonzero : ((‖position‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr nonzero
  have phase : (‖position‖ : ℂ) * Complex.exp (Complex.I * (Complex.arg position : ℂ)) = position := by
    simpa only [mul_comm] using Complex.norm_mul_exp_arg_mul_I position
  have product : Complex.exp (Complex.I * (Complex.arg position : ℂ)) * star position = (‖position‖ : ℂ) := by
    apply mul_left_cancel₀ normNonzero
    rw [← mul_assoc, phase]
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two,
      Complex.ofReal_mul] using Complex.mul_conj position
  have exponential : Complex.exp (4 * Complex.I * (Complex.arg position : ℂ)) =
      Complex.exp (Complex.I * (Complex.arg position : ℂ)) ^ 4 := by
    convert Complex.exp_nat_mul (Complex.I * (Complex.arg position : ℂ)) 4 using 1 <;> congr 1 <;> ring
  rw [exponential]
  apply (div_eq_div_iff (pow_ne_zero 4 (star_ne_zero.mpr nonzero)) (pow_ne_zero 4 normNonzero)).mpr
  have powered := congrArg (fun value : ℂ => value ^ 4) product
  change (Complex.exp (Complex.I * (Complex.arg position : ℂ)) * star position) ^ 4 =
    (‖position‖ : ℂ) ^ 4 at powered
  rw [mul_pow] at powered
  simpa only [one_mul] using powered.symm

def separatingLeadingMoment (circulation outgoingPhase time : ℝ) : ℂ :=
  -(2 * Complex.I / (Real.pi : ℂ)) * (circulation : ℂ) ^ 2 *
    Complex.exp (2 * Complex.I * (outgoingPhase : ℂ)) * (time : ℂ)

theorem leadingSourceStrain_eq_moment (circulation outgoingPhase time : ℝ) {position : ℂ}
    (nonzero : position ≠ 0) :
    leadingSourceStrain circulation ‖position‖ (Complex.arg position) outgoingPhase time =
      -3 * Complex.I * star (separatingLeadingMoment circulation outgoingPhase time) /
        (2 * (Real.pi : ℂ) * star position ^ 4) := by
  have inverseIdentity := inverse_conjugate_fourth_phase nonzero
  unfold leadingSourceStrain separatingLeadingMoment
  simp only [star_mul, star_neg, star_div₀, star_pow, Complex.star_def, map_mul,
    Complex.conj_ofReal, Complex.conj_ofNat, Complex.conj_I, ← Complex.exp_conj]
  push_cast
  simp only [← Complex.star_def]
  rw [show -3 * Complex.I *
      ((time : ℂ) * (Complex.exp (2 * -Complex.I * (outgoingPhase : ℂ)) *
        ((circulation : ℂ) ^ 2 * -(-Complex.I * 2 / (Real.pi : ℂ))))) /
        (2 * (Real.pi : ℂ) * star position ^ 4) =
      (3 * (circulation : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) * (time : ℂ) *
        Complex.exp (2 * -Complex.I * (outgoingPhase : ℂ)) * (1 / star position ^ 4) by
          ring_nf; simp [Complex.I_sq]]
  rw [inverseIdentity]
  rw [show (3 * (circulation : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) * (time : ℂ) *
      Complex.exp (2 * -Complex.I * (outgoingPhase : ℂ)) *
      (Complex.exp (4 * Complex.I * (Complex.arg position : ℂ)) / (‖position‖ : ℂ) ^ 4) =
      (3 * (circulation : ℂ) ^ 2 / ((Real.pi : ℂ) ^ 2 * (‖position‖ : ℂ) ^ 4)) * (time : ℂ) *
        (Complex.exp (2 * -Complex.I * (outgoingPhase : ℂ)) *
          Complex.exp (4 * Complex.I * (Complex.arg position : ℂ))) by ring]
  rw [← Complex.exp_add]
  congr 2
  ring

theorem quadrupoleExternalStrain_leading_error (circulation outgoingPhase time : ℝ)
    {first second position : ℂ} (positionNonzero : position ≠ 0)
    (firstSmall : ‖first‖ ≤ ‖position‖ / 2) (secondSmall : ‖second‖ ≤ ‖position‖ / 2)
    {momentError : ℝ}
    (momentEstimate : ‖quadrupoleComplexMoment circulation first second -
      separatingLeadingMoment circulation outgoingPhase time‖ ≤ momentError) :
    ‖quadrupoleExternalStrain circulation first second position -
      leadingSourceStrain circulation ‖position‖ (Complex.arg position) outgoingPhase time‖ ≤
      (20 / Real.pi) * ‖quadrupoleComplexMoment circulation first second‖ *
        (‖first‖ ^ 2 + ‖second‖ ^ 2) / ‖position‖ ^ 6 +
      3 * momentError / (2 * Real.pi * ‖position‖ ^ 4) := by
  have identity : quadrupoleExternalStrain circulation first second position -
      leadingSourceStrain circulation ‖position‖ (Complex.arg position) outgoingPhase time =
      (quadrupoleExternalStrain circulation first second position +
        3 * Complex.I * star (quadrupoleComplexMoment circulation first second) /
          (2 * (Real.pi : ℂ) * star position ^ 4)) -
      3 * Complex.I * star (quadrupoleComplexMoment circulation first second -
        separatingLeadingMoment circulation outgoingPhase time) /
          (2 * (Real.pi : ℂ) * star position ^ 4) := by
    rw [leadingSourceStrain_eq_moment _ _ _ positionNonzero, star_sub]
    ring
  rw [identity]
  apply (norm_sub_le _ _).trans
  apply add_le_add (quadrupoleExternalStrain_error circulation positionNonzero firstSmall secondSmall)
  simp only [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul, mul_one,
    norm_star, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left momentEstimate (by norm_num)) (by positivity)

theorem physical_separating_source_strain_error (length circulation : ℝ)
    (lengthPositive : 0 < length) (circulationPositive : 0 < circulation) :
    let frequency : ℝ := circulation / (2 * Real.pi * length ^ 2)
    let frequencyPositive : 0 < frequency := by dsimp [frequency]; positivity
    let positive := fun time => (length : ℂ) * separatingPositive frequency frequencyPositive time
    let negative := fun time => (length : ℂ) * separatingNegative frequency frequencyPositive time
    ∃ angle : ℝ, ∃ momentOffset : ℂ, ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ),
      ∀ time, timeMin ≤ time → ∀ position : ℂ, position ≠ 0 →
      ‖positive time‖ ≤ ‖position‖ / 2 → ‖negative time‖ ≤ ‖position‖ / 2 →
      ‖quadrupoleExternalStrain circulation (positive time) (negative time) position -
        leadingSourceStrain circulation ‖position‖ (Complex.arg position) angle time‖ ≤
        (20 / Real.pi) * ‖quadrupoleComplexMoment circulation (positive time) (negative time)‖ *
          (‖positive time‖ ^ 2 + ‖negative time‖ ^ 2) / ‖position‖ ^ 6 +
        3 * (‖momentOffset‖ + bound / time) / (2 * Real.pi * ‖position‖ ^ 4) := by
  dsimp only
  obtain ⟨angle, offset, bound, boundPositive, timeMin, timePositive, estimate⟩ :=
    physical_separating_moment_growth length circulation lengthPositive circulationPositive
  refine ⟨angle, offset, bound, boundPositive, timeMin, timePositive, ?_⟩
  intro time timeAbove position positionNonzero firstSmall secondSmall
  apply quadrupoleExternalStrain_leading_error circulation angle time positionNonzero firstSmall secondSmall
  have growth := estimate time timeAbove
  let moment := quadrupoleComplexMoment circulation
    ((length : ℂ) * separatingPositive (circulation / (2 * Real.pi * length ^ 2)) (by positivity) time)
    ((length : ℂ) * separatingNegative (circulation / (2 * Real.pi * length ^ 2)) (by positivity) time)
  have errorIdentity : moment - separatingLeadingMoment circulation angle time - offset =
      moment + (2 * Complex.I / (Real.pi : ℂ)) * (circulation : ℂ) ^ 2 *
        Complex.exp (2 * Complex.I * (angle : ℂ)) * (time : ℂ) - offset := by
    unfold separatingLeadingMoment
    ring
  change ‖moment - separatingLeadingMoment circulation angle time‖ ≤ ‖offset‖ + bound / time
  calc
    _ ≤ ‖moment - separatingLeadingMoment circulation angle time - offset‖ + ‖offset‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (moment - separatingLeadingMoment circulation angle time - offset) offset
    _ ≤ bound / time + ‖offset‖ := by
      apply add_le_add_right _ _
      rw [errorIdentity]
      exact growth
    _ = _ := by ring

end EulerNonuniqueness.Section6
