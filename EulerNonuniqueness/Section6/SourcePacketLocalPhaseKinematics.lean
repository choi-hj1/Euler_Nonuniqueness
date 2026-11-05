import EulerNonuniqueness.General.PhaseDilationControl
import EulerNonuniqueness.Section6.RhombusStrain

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem source_packet_local_phase_increment_bound
    {phase dilation remainder : ℝ → ℝ} {frequency horizon diagonalError phaseError : ℝ}
    (frequencyPositive : 0 < frequency) (horizonNonnegative : 0 ≤ horizon)
    (diagonalNonnegative : 0 ≤ diagonalError) (phaseNonnegative : 0 ≤ phaseError)
    (equation : ∀ elapsed ∈ Icc 0 horizon,
      HasDerivAt phase (-frequency / dilation elapsed + remainder elapsed) elapsed)
    (lower : ∀ elapsed ∈ Icc 0 horizon, 1 / 2 ≤ dilation elapsed)
    (diagonalBound : ∀ elapsed ∈ Icc 0 horizon, |dilation elapsed - 1| ≤ diagonalError)
    (remainderBound : ∀ elapsed ∈ Icc 0 horizon, |remainder elapsed| ≤ frequency * phaseError) :
    ∀ elapsed ∈ Icc 0 horizon,
      |phase elapsed - phase 0 + frequency * elapsed| ≤ frequency * (2 * diagonalError + phaseError) * elapsed := by
  have rateNonnegative : 0 ≤ frequency * (2 * diagonalError + phaseError) := by positivity
  have derivative (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      HasDerivWithinAt (fun current => phase current + frequency * current)
        ((-frequency / dilation elapsed + remainder elapsed) + frequency) (Icc 0 horizon) elapsed := by
    simpa only [mul_one] using ((equation elapsed inside).add ((hasDerivAt_id elapsed).const_mul frequency)).hasDerivWithinAt
  have slope (elapsed : ℝ) (inside : elapsed ∈ Ico 0 horizon) :
      ‖(-frequency / dilation elapsed + remainder elapsed) + frequency‖ ≤ frequency * (2 * diagonalError + phaseError) := by
    have inside : elapsed ∈ Icc 0 horizon := ⟨inside.1, inside.2.le⟩
    have dilationPositive : 0 < dilation elapsed := by linarith [lower elapsed inside]
    have inverseIdentity : -frequency / dilation elapsed + frequency =
        frequency * (dilation elapsed - 1) / dilation elapsed := by field_simp; ring
    have inverseBound : |-frequency / dilation elapsed + frequency| ≤ 2 * frequency * diagonalError := by
      rw [inverseIdentity, abs_div, abs_mul, abs_of_pos frequencyPositive, abs_of_pos dilationPositive]
      apply (div_le_iff₀ dilationPositive).mpr
      have first := mul_le_mul_of_nonneg_left (diagonalBound elapsed inside) frequencyPositive.le
      have second := mul_le_mul_of_nonneg_left (lower elapsed inside)
        (show 0 ≤ 2 * frequency * diagonalError by positivity)
      nlinarith
    rw [Real.norm_eq_abs]
    have identity : (-frequency / dilation elapsed + remainder elapsed) + frequency =
        (-frequency / dilation elapsed + frequency) + remainder elapsed := by ring
    rw [identity]
    exact (abs_add _ _).trans ((add_le_add inverseBound (remainderBound elapsed inside)).trans_eq (by ring))
  intro elapsed inside
  have bound := norm_image_sub_le_of_norm_deriv_le_segment' derivative slope elapsed inside
  have arrangement : phase elapsed + frequency * elapsed - phase 0 = phase elapsed - phase 0 + frequency * elapsed := by ring
  simp only [mul_zero, add_zero, arrangement] at bound
  simpa only [Real.norm_eq_abs, mul_zero, add_zero, sub_zero] using bound

theorem source_packet_phase_exponential_difference (first second : ℝ) :
    ‖Complex.exp (-2 * Complex.I * (first : ℂ)) - Complex.exp (-2 * Complex.I * (second : ℂ))‖ ≤
      2 * |first - second| := by
  let function : ℝ → ℂ := fun value => Complex.exp (-2 * Complex.I * (value : ℂ))
  have derivative (value : ℝ) : HasDerivAt function
      ((-2 * Complex.I) * Complex.exp (-2 * Complex.I * (value : ℂ))) value := by
    convert ((((hasDerivAt_id value).ofReal_comp).const_mul (-2 * Complex.I)).cexp) using 1 <;>
      simp only [id_eq, Complex.ofReal_one, mul_one] <;> ring
  have bound (value : ℝ) : ‖deriv function value‖ ≤ 2 := by
    rw [(derivative value).deriv, norm_mul, Complex.norm_exp]
    norm_num
  have estimate := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ)
    (fun value _ => (derivative value).differentiableAt) (fun value _ => bound value)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ second) (mem_univ first)
  simpa only [Real.norm_eq_abs] using estimate

end EulerNonuniqueness.Paper
