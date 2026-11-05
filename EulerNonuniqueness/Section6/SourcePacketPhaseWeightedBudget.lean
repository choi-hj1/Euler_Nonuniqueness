import EulerNonuniqueness.Section6.SourcePacketRetainedTargetMoment
import EulerNonuniqueness.Section6.SourcePacketLocalPhaseKinematics

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem source_packet_laplace_quadratic_bound {decay quadratic linear horizon : ℝ}
    (decayPositive : 0 < decay) (quadraticNonnegative : 0 ≤ quadratic) (linearNonnegative : 0 ≤ linear)
    (horizonNonnegative : 0 ≤ horizon) :
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * (quadratic * elapsed ^ 2 + linear * elapsed)) ≤
      2 * quadratic / decay ^ 3 + linear / decay ^ 2 := by
  let primitive := fun elapsed => -(Real.exp (-decay * elapsed) *
    (quadratic * (decay ^ 2 * elapsed ^ 2 + 2 * decay * elapsed + 2) + linear * decay * (decay * elapsed + 1))) / decay ^ 3
  have derivative (elapsed : ℝ) : HasDerivAt primitive
      (Real.exp (-decay * elapsed) * (quadratic * elapsed ^ 2 + linear * elapsed)) elapsed := by
    have exponential := (((hasDerivAt_id elapsed).const_mul (-decay)).exp)
    have polynomial : HasDerivAt (fun current : ℝ => quadratic * (decay ^ 2 * current ^ 2 + 2 * decay * current + 2) +
        linear * decay * (decay * current + 1))
        (quadratic * (decay ^ 2 * (2 * elapsed) + 2 * decay) + linear * decay * decay) elapsed := by
      convert ((((((hasDerivAt_id elapsed).pow 2).const_mul (decay ^ 2)).add
        ((hasDerivAt_id elapsed).const_mul (2 * decay))).add_const 2).const_mul quadratic).add
        ((((hasDerivAt_id elapsed).const_mul decay).add_const 1).const_mul (linear * decay)) using 1 <;>
        simp only [id_eq] <;> ring
    convert (exponential.mul polynomial).neg.div_const (decay ^ 3) using 1
    dsimp only
    field_simp [decayPositive.ne'] <;> ring
  have integrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      (quadratic * elapsed ^ 2 + linear * elapsed)) volume 0 horizon := by
    apply Continuous.intervalIntegrable
    fun_prop
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun elapsed _ => derivative elapsed) integrable
  have initial : primitive 0 = -(2 * quadratic / decay ^ 3 + linear / decay ^ 2) := by
    dsimp only [primitive]
    simp only [mul_zero, Real.exp_zero, zero_add, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_one]
    field_simp [decayPositive.ne'] <;> ring
  have terminal : primitive horizon ≤ 0 := by
    dsimp only [primitive]
    apply div_nonpos_of_nonpos_of_nonneg _ (pow_nonneg decayPositive.le 3)
    exact neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le (by positivity))
  rw [initial] at identity
  linarith

theorem Scales.source_packet_retained_phase_cost_bound (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (moment : ℂ) (outgoingPhase horizon distance tolerance : ℝ) (orientation : ℝ → ℂ)
    (orientationContinuous : Continuous orientation) (horizonNonnegative : 0 ≤ horizon)
    (distancePositive : 0 < distance) (toleranceNonnegative : 0 ≤ tolerance)
    (orientationBound : ∀ elapsed ∈ Icc 0 horizon,
      ‖orientation elapsed‖ ≤ 2 * tolerance * scales.omega index * elapsed)
    (inheritedBound : 6 * ‖moment‖ / (Real.pi * distance ^ 4 * (2 * Real.sqrt 2 * scales.omega index)) ≤
      Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) :
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * scales.omega index) * elapsed) *
      ((6 / (Real.pi * distance ^ 4)) *
        ‖moment + separatingLeadingMoment (scales.circulation (index + 1)) outgoingPhase elapsed‖ * ‖orientation elapsed‖)) ≤
      8 * tolerance * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  let omega := scales.omega index
  let circulation := scales.circulation (index + 1)
  let decay := 2 * Real.sqrt 2 * omega
  let seed := Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * distance ^ 4)
  let coefficient := 6 / (Real.pi * distance ^ 4)
  let slope := 2 * circulation ^ 2 / Real.pi
  have omegaPositive : 0 < omega := scales.omega_pos frequencyPositive ratioPositive _
  have circulationPositive : 0 < circulation := scales.circulation_pos frequencyPositive ratioPositive _
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have slopeNonnegative : 0 ≤ slope := by dsimp only [slope]; positivity
  have exponentialNorm : ‖Complex.exp (2 * Complex.I * (outgoingPhase : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
  have rampNorm (elapsed : ℝ) (nonnegative : 0 ≤ elapsed) :
      ‖separatingLeadingMoment circulation outgoingPhase elapsed‖ = slope * elapsed := by
    simp only [separatingLeadingMoment, norm_mul, norm_neg, norm_div, norm_pow, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, exponentialNorm, abs_of_pos Real.pi_pos,
      abs_of_pos circulationPositive, abs_of_nonneg nonnegative]
    dsimp only [slope]
    norm_num
    ring <;> simp
  have targetBound (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖moment + separatingLeadingMoment circulation outgoingPhase elapsed‖ ≤ ‖moment‖ + slope * elapsed := by
    exact (norm_add_le _ _).trans_eq (by rw [rampNorm elapsed inside.1])
  have actualContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) *
      (coefficient * ‖moment + separatingLeadingMoment circulation outgoingPhase elapsed‖ * ‖orientation elapsed‖)) := by
    unfold separatingLeadingMoment
    fun_prop
  have majorantContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) *
      ((coefficient * slope * (2 * tolerance * omega)) * elapsed ^ 2 +
        (coefficient * ‖moment‖ * (2 * tolerance * omega)) * elapsed)) := by fun_prop
  have integrated := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative
    (actualContinuous.intervalIntegrable 0 horizon) (majorantContinuous.intervalIntegrable 0 horizon) (fun elapsed inside => by
      have elapsedNonnegative := inside.1
      have bound := mul_le_mul (mul_le_mul_of_nonneg_left (targetBound elapsed inside) coefficientNonnegative)
        (orientationBound elapsed inside) (norm_nonneg _) (by positivity : 0 ≤ coefficient * (‖moment‖ + slope * elapsed))
      have weighted := mul_le_mul_of_nonneg_left bound (Real.exp_pos (-decay * elapsed)).le
      convert weighted using 1 <;> ring)
  have numeric := source_packet_laplace_quadratic_bound decayPositive
    (show 0 ≤ coefficient * slope * (2 * tolerance * omega) by positivity)
    (show 0 ≤ coefficient * ‖moment‖ * (2 * tolerance * omega) by positivity) horizonNonnegative
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtTwoOne : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have initialScaled := mul_le_mul_of_nonneg_left inheritedBound (show 0 ≤ tolerance by positivity)
  have initialCost : (coefficient * ‖moment‖ * (2 * tolerance * omega)) / decay ^ 2 ≤ tolerance * seed := by
    have first : (coefficient * ‖moment‖ * (2 * tolerance * omega)) / decay ^ 2 =
        (tolerance / Real.sqrt 2) * (6 * ‖moment‖ / (Real.pi * distance ^ 4 * decay)) := by
      dsimp only [coefficient, decay]
      field_simp [Real.pi_ne_zero, distancePositive.ne', omegaPositive.ne', sqrtTwoPositive.ne'] <;> ring
    rw [first]
    have baseNonnegative : 0 ≤ 6 * ‖moment‖ / (Real.pi * distance ^ 4 * decay) := by positivity
    have scalar : tolerance / Real.sqrt 2 ≤ tolerance := by
      exact (div_le_self toleranceNonnegative sqrtTwoOne)
    exact (mul_le_mul_of_nonneg_right scalar baseNonnegative).trans initialScaled
  have leadingCost : 2 * (coefficient * slope * (2 * tolerance * omega)) / decay ^ 3 ≤ 6 * tolerance * seed := by
    have squareTwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have sqrtThreeOne : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    let common := 3 * tolerance * circulation ^ 2 / (Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * distance ^ 4)
    have commonNonnegative : 0 ≤ common := by dsimp only [common]; positivity
    have identity : 2 * (coefficient * slope * (2 * tolerance * omega)) / decay ^ 3 = common := by
      dsimp only [coefficient, slope, decay, common]
      have cubeTwo : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
        calc
          _ = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
          _ = _ := by rw [squareTwo]
      simp only [mul_pow, cubeTwo]
      field_simp [Real.pi_ne_zero, distancePositive.ne', omegaPositive.ne', sqrtTwoPositive.ne'] <;> ring
    rw [identity]
    have comparison := mul_le_mul_of_nonneg_right sqrtThreeOne commonNonnegative
    convert comparison using 1 <;> dsimp only [common, seed] <;> ring
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  exact integrated.trans (numeric.trans ((add_le_add leadingCost initialCost).trans (by nlinarith)))

end EulerNonuniqueness.Paper
