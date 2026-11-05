import EulerNonuniqueness.Section6.SourcePacketMomentInheritance
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.retained_target_moment_weighted_bound (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (moment : ℂ) (outgoingPhase horizon distance budget : ℝ)
    (horizonNonnegative : 0 ≤ horizon) (distancePositive : 0 < distance)
    (inheritedBound : 6 * ‖moment‖ / (Real.pi * distance ^ 4 * (2 * Real.sqrt 2 * scales.omega index)) ≤
      budget * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4))) :
    (6 / (Real.pi * distance ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * scales.omega index) * elapsed) *
        ‖moment + separatingLeadingMoment (scales.circulation (index + 1)) outgoingPhase elapsed‖) ≤
      (budget + 3) * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have decayPositive : 0 < 2 * Real.sqrt 2 * scales.omega index := by positivity
  have exponentialNorm : ‖Complex.exp (2 * Complex.I * (outgoingPhase : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have rampNorm (elapsed : ℝ) (nonnegative : 0 ≤ elapsed) :
      ‖separatingLeadingMoment (scales.circulation (index + 1)) outgoingPhase elapsed‖ =
        (2 * scales.circulation (index + 1) ^ 2 / Real.pi) * elapsed := by
    simp only [separatingLeadingMoment, norm_mul, norm_neg, norm_div, norm_pow, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, exponentialNorm, abs_of_pos Real.pi_pos,
      abs_of_pos circulationPositive, abs_of_nonneg nonnegative]
    norm_num
    ring <;> simp
  have targetContinuous : Continuous (fun elapsed : ℝ => moment +
      separatingLeadingMoment (scales.circulation (index + 1)) outgoingPhase elapsed) := by
    unfold separatingLeadingMoment
    fun_prop
  have weighted := laplace_norm_error_integral_bound targetContinuous decayPositive
    (show 0 ≤ 2 * scales.circulation (index + 1) ^ 2 / Real.pi by positivity) (norm_nonneg _) horizonNonnegative
    (fun elapsed inside => (norm_add_le _ _).trans_eq (by rw [rampNorm elapsed inside.1]; ring))
  let common := scales.circulation (index + 1) ^ 2 /
    (Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)
  have commonNonnegative : 0 ≤ common := by dsimp only [common]; positivity
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have squareTwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have leadingIdentity : (6 / (Real.pi * distance ^ 4)) *
      ((2 * scales.circulation (index + 1) ^ 2 / Real.pi) / (2 * Real.sqrt 2 * scales.omega index) ^ 2) =
      (3 / 2 : ℝ) * common := by
    dsimp only [common]
    simp only [mul_pow, squareTwo]
    field_simp [Real.pi_ne_zero, distancePositive.ne', receiverPositive.ne', sqrtTwoPositive.ne']
    <;> ring
  have coefficient : (3 / 2 : ℝ) ≤ 3 * Real.sqrt 3 / (2 * Real.sqrt 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt 2)).mpr
    nlinarith [Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 3)]
  have leadingBound := mul_le_mul_of_nonneg_right coefficient commonNonnegative
  have multiplied := mul_le_mul_of_nonneg_left weighted (show 0 ≤ 6 / (Real.pi * distance ^ 4) by positivity)
  rw [mul_add, leadingIdentity] at multiplied
  have initial : (6 / (Real.pi * distance ^ 4)) * (‖moment‖ / (2 * Real.sqrt 2 * scales.omega index)) ≤
      budget * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
    convert inheritedBound using 1 <;> ring
  have combined := add_le_add leadingBound initial
  exact multiplied.trans (by convert combined using 1 <;> dsimp only [common] <;> ring)

end EulerNonuniqueness.Paper
