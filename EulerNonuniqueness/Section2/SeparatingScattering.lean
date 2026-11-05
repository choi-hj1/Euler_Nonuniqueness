import EulerNonuniqueness.Section2.SeparatingReconstruction

noncomputable section

namespace EulerNonuniqueness.Section2

def separatingDipoleSeparation (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) : ℂ :=
  separatingPositive frequency frequencyPositive time + separatingNegative frequency frequencyPositive time

def separatingDipoleCenter (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) : ℂ :=
  (separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time) / 2

theorem separatingNegative_ne_zero (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    separatingNegative frequency frequencyPositive time ≠ 0 := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  apply norm_ne_zero_iff.mp
  rw [separatingNegative_norm]
  exact mul_ne_zero (norm_ne_zero_iff.mpr (separatingPositive_ne_zero frequency frequencyPositive time)) rootPositive.ne'

theorem separating_pair_ne_zero (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time ≠ 0 ∧
    separatingPositive frequency frequencyPositive time + separatingNegative frequency frequencyPositive time ≠ 0 := by
  obtain ⟨minimum, minimumPositive, minimumProperty⟩ := separating_uniform_noncollision frequency frequencyPositive
  have bounds := minimumProperty time
  exact ⟨norm_ne_zero_iff.mp (ne_of_gt (minimumPositive.trans_le bounds.2.2.1)),
    norm_ne_zero_iff.mp (ne_of_gt (minimumPositive.trans_le bounds.2.2.2))⟩

theorem separating_dipole_sum_algebra (frequency first second : ℂ)
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0)
    (differenceNonzero : first - second ≠ 0) (sumNonzero : first + second ≠ 0) :
    -Complex.I * frequency * (3 * first ^ 2 + second ^ 2) /
      (2 * first * (first ^ 2 - second ^ 2)) +
      -Complex.I * frequency * (first ^ 2 + 3 * second ^ 2) /
        (2 * second * (first ^ 2 - second ^ 2)) =
      -Complex.I * frequency * (first + second) ^ 2 /
        (2 * first * second * (first - second)) := by
  simp only [show first ^ 2 - second ^ 2 = (first - second) * (first + second) by ring]
  field_simp [firstNonzero, secondNonzero, differenceNonzero, sumNonzero]
  <;> ring

theorem separating_dipole_center_algebra (frequency first second : ℂ)
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0)
    (differenceNonzero : first - second ≠ 0) (sumNonzero : first + second ≠ 0) :
    (-Complex.I * frequency * (3 * first ^ 2 + second ^ 2) /
      (2 * first * (first ^ 2 - second ^ 2)) -
      -Complex.I * frequency * (first ^ 2 + 3 * second ^ 2) /
        (2 * second * (first ^ 2 - second ^ 2))) / 2 =
      -Complex.I * frequency / (first + second) +
        Complex.I * frequency * (first + second) / (4 * first * second) := by
  have squareNonzero : first ^ 2 - second ^ 2 ≠ 0 := by
    rw [show first ^ 2 - second ^ 2 = (first - second) * (first + second) by ring]
    exact mul_ne_zero differenceNonzero sumNonzero
  generalize squareDefinition : first ^ 2 - second ^ 2 = squareDifference at *
  generalize sumDefinition : first + second = sum at *
  field_simp [firstNonzero, secondNonzero, squareNonzero, sumNonzero]
  have denominatorNonzero : 2 * first * squareDifference * (2 * second * squareDifference) * 2 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) firstNonzero) squareNonzero)
        (mul_ne_zero (mul_ne_zero (by norm_num) secondNonzero) squareNonzero)) (by norm_num)
  apply (div_eq_iff denominatorNonzero).mpr
  rw [← squareDefinition, ← sumDefinition]
  ring

theorem separatingDipoleSeparation_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingDipoleSeparation frequency frequencyPositive)
      (-Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) ^ 2 /
        (2 * star (separatingPositive frequency frequencyPositive time) *
          star (separatingNegative frequency frequencyPositive time) *
          star (separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time))) time := by
  have pairs := separating_pair_ne_zero frequency frequencyPositive time
  have derivative := (separatingPositive_pointEquation frequency frequencyPositive time).add
    (separatingNegative_pointEquation frequency frequencyPositive time)
  rw [separating_dipole_sum_algebra _ _ _
    (star_ne_zero.mpr (separatingPositive_ne_zero frequency frequencyPositive time))
    (star_ne_zero.mpr (separatingNegative_ne_zero frequency frequencyPositive time))
    (by simpa only [← star_sub] using star_ne_zero.mpr pairs.1)
    (by simpa only [← star_add] using star_ne_zero.mpr pairs.2)] at derivative
  simpa only [separatingDipoleSeparation, star_add, star_sub] using derivative

theorem separatingDipoleCenter_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingDipoleCenter frequency frequencyPositive)
      (-Complex.I * (frequency : ℂ) / star (separatingDipoleSeparation frequency frequencyPositive time) +
        Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) /
          (4 * star (separatingPositive frequency frequencyPositive time) *
            star (separatingNegative frequency frequencyPositive time))) time := by
  have pairs := separating_pair_ne_zero frequency frequencyPositive time
  have derivative := ((separatingPositive_pointEquation frequency frequencyPositive time).sub
    (separatingNegative_pointEquation frequency frequencyPositive time)).div_const 2
  rw [separating_dipole_center_algebra _ _ _
    (star_ne_zero.mpr (separatingPositive_ne_zero frequency frequencyPositive time))
    (star_ne_zero.mpr (separatingNegative_ne_zero frequency frequencyPositive time))
    (by simpa only [← star_sub] using star_ne_zero.mpr pairs.1)
    (by simpa only [← star_add] using star_ne_zero.mpr pairs.2)] at derivative
  simpa only [separatingDipoleCenter, separatingDipoleSeparation, star_add] using derivative

theorem separatingDipoleSeparation_norm_bounds (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    1 ≤ ‖separatingDipoleSeparation frequency frequencyPositive time‖ ∧
      ‖separatingDipoleSeparation frequency frequencyPositive time‖ ≤ 2 := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have square := (separating_pair_distance_squares frequency frequencyPositive time).1
  change ‖separatingDipoleSeparation frequency frequencyPositive time‖ ^ 2 = _ at square
  have lowerSquare : 1 ≤ ‖separatingDipoleSeparation frequency frequencyPositive time‖ ^ 2 := by
    rw [square]
    apply (le_div_iff₀ (by linarith : 0 < 1 + separatingScalarOrbit frequency frequencyPositive time)).mpr
    linarith [bounds.2]
  have upperSquare : ‖separatingDipoleSeparation frequency frequencyPositive time‖ ^ 2 ≤ 2 := by
    rw [square]
    apply (div_le_iff₀ (by linarith : 0 < 1 + separatingScalarOrbit frequency frequencyPositive time)).mpr
    linarith
  constructor <;> nlinarith [norm_nonneg (separatingDipoleSeparation frequency frequencyPositive time)]

theorem separatingDipoleSeparation_norm_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => ‖separatingDipoleSeparation frequency frequencyPositive time‖)
      Filter.atTop (nhds 1) := by
  have scalarLimit := separatingScalarOrbit_outgoing_limit frequency frequencyPositive
  have result := ((tendsto_const_nhds.div (tendsto_const_nhds.add scalarLimit)
    (by norm_num : (1 + 1 : ℝ) ≠ 0)) : Filter.Tendsto
      (fun time => 2 / (1 + separatingScalarOrbit frequency frequencyPositive time))
      Filter.atTop (nhds (2 / (1 + 1 : ℝ))))
  have squareRootLimit := Real.continuous_sqrt.continuousAt.tendsto.comp result
  norm_num at squareRootLimit
  apply squareRootLimit.congr'
  apply Filter.Eventually.of_forall
  intro time
  have square := (separating_pair_distance_squares frequency frequencyPositive time).1
  change Real.sqrt (2 / (1 + separatingScalarOrbit frequency frequencyPositive time)) = _
  rw [← square, Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem separating_large_norm_lower (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    (Real.sqrt 2 - 1) * ‖separatingPositive frequency frequencyPositive time‖ ≤
      ‖separatingNegative frequency frequencyPositive time‖ ∧
    (Real.sqrt 2 - 1) * ‖separatingPositive frequency frequencyPositive time‖ ≤
      ‖separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time‖ := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have minimumPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have minimumBelowOne : Real.sqrt 2 - 1 < 1 := by linarith [sqrt_two_lt_three_halves]
  constructor
  · rw [separatingNegative_norm, mul_comm (Real.sqrt 2 - 1)]
    exact mul_le_mul_of_nonneg_left bounds.1.le (norm_nonneg _)
  · have ratioSquare := (separatingComplexRatio_pair_normSq bounds.1 bounds.2).2
    rw [Complex.normSq_eq_norm_sq] at ratioSquare
    have ratioLower : Real.sqrt 2 - 1 ≤
        ‖1 - separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time)‖ := by
      nlinarith [norm_nonneg (1 - separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time)), bounds.1]
    rw [separatingNegative, ← mul_one_sub, norm_mul, mul_comm (Real.sqrt 2 - 1)]
    exact mul_le_mul_of_nonneg_left ratioLower (norm_nonneg _)

theorem separatingDipoleSeparation_velocity_decay (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ), ∀ time, timeMin < time →
      ‖-Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) ^ 2 /
        (2 * star (separatingPositive frequency frequencyPositive time) *
          star (separatingNegative frequency frequencyPositive time) *
          star (separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time))‖ ≤
        bound / time ^ 3 := by
  have minimumPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  obtain ⟨timeMin, timePositive, coordinateLower⟩ :=
    separatingEscapeCoordinate_linear_lower frequency frequencyPositive
  refine ⟨frequency * 4 / (2 * (Real.sqrt 2 - 1) ^ 2 * (frequency / 4) ^ 3), by positivity,
    timeMin, timePositive, ?_⟩
  intro time timeAbove
  have timePositive' : 0 < time := timePositive.trans timeAbove
  have positiveLower : frequency / 4 * time ≤ ‖separatingPositive frequency frequencyPositive time‖ := by
    simpa only [separatingEscapeCoordinate, separatingPositive_norm] using coordinateLower time timeAbove.le
  have largeLower := separating_large_norm_lower frequency frequencyPositive time
  have negativeLower : (Real.sqrt 2 - 1) * (frequency / 4 * time) ≤
      ‖separatingNegative frequency frequencyPositive time‖ :=
    (mul_le_mul_of_nonneg_left positiveLower minimumPositive.le).trans largeLower.1
  have differenceLower : (Real.sqrt 2 - 1) * (frequency / 4 * time) ≤
      ‖separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time‖ :=
    (mul_le_mul_of_nonneg_left positiveLower minimumPositive.le).trans largeLower.2
  have separationBound := (separatingDipoleSeparation_norm_bounds frequency frequencyPositive time).2
  have numeratorBound : frequency * ‖separatingDipoleSeparation frequency frequencyPositive time‖ ^ 2 ≤ frequency * 4 := by
    apply mul_le_mul_of_nonneg_left _ frequencyPositive.le
    nlinarith [norm_nonneg (separatingDipoleSeparation frequency frequencyPositive time)]
  have denominatorBound : 2 * (frequency / 4 * time) *
      ((Real.sqrt 2 - 1) * (frequency / 4 * time)) * ((Real.sqrt 2 - 1) * (frequency / 4 * time)) ≤
      2 * ‖separatingPositive frequency frequencyPositive time‖ * ‖separatingNegative frequency frequencyPositive time‖ *
        ‖separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time‖ := by
    gcongr
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_pow, norm_star,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyPositive]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ frequency * 4 / (2 * (frequency / 4 * time) *
      ((Real.sqrt 2 - 1) * (frequency / 4 * time)) * ((Real.sqrt 2 - 1) * (frequency / 4 * time))) := by
      apply div_le_div₀ (by positivity) numeratorBound (by positivity) denominatorBound
    _ = _ := by field_simp; ring

theorem separatingDipoleSeparation_scattering (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ limit : ℂ, ‖limit‖ = 1 ∧
      Filter.Tendsto (separatingDipoleSeparation frequency frequencyPositive) Filter.atTop (nhds limit) ∧
      ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ), ∀ time, timeMin < time →
        ‖separatingDipoleSeparation frequency frequencyPositive time - limit‖ ≤ bound / time ^ 2 := by
  obtain ⟨bound, boundPositive, timeMin, timePositive, decayProperty⟩ :=
    separatingDipoleSeparation_velocity_decay frequency frequencyPositive
  obtain ⟨limit, limitProperty, errorProperty⟩ := complex_atTop_quadratic_error timePositive
    boundPositive.le (fun time _ => separatingDipoleSeparation_hasDerivAt frequency frequencyPositive time) decayProperty
  refine ⟨limit, ?_, limitProperty, bound, boundPositive, timeMin, timePositive, errorProperty⟩
  exact tendsto_nhds_unique limitProperty.norm (separatingDipoleSeparation_norm_limit frequency frequencyPositive)


theorem complex_inverse_difference_le {first second : ℂ}
    (firstLower : 1 ≤ ‖first‖) (secondLower : 1 ≤ ‖second‖) :
    ‖first⁻¹ - second⁻¹‖ ≤ ‖first - second‖ := by
  have firstPositive : 0 < ‖first‖ := by linarith
  have secondPositive : 0 < ‖second‖ := by linarith
  have productLower : 1 ≤ ‖first‖ * ‖second‖ := by nlinarith
  rw [← dist_eq_norm, dist_inv_inv₀ (norm_ne_zero_iff.mp firstPositive.ne')
    (norm_ne_zero_iff.mp secondPositive.ne'), dist_eq_norm]
  apply (div_le_iff₀ (mul_pos firstPositive secondPositive)).mpr
  exact le_mul_of_one_le_right (norm_nonneg _) productLower

theorem separatingDipoleCenter_remainder_decay (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ), ∀ time, timeMin < time →
      ‖Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) /
        (4 * star (separatingPositive frequency frequencyPositive time) *
          star (separatingNegative frequency frequencyPositive time))‖ ≤ bound / time ^ 2 := by
  have minimumPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  obtain ⟨timeMin, timePositive, coordinateLower⟩ :=
    separatingEscapeCoordinate_linear_lower frequency frequencyPositive
  refine ⟨frequency * 2 / (4 * (Real.sqrt 2 - 1) * (frequency / 4) ^ 2), by positivity,
    timeMin, timePositive, ?_⟩
  intro time timeAbove
  have timePositive' : 0 < time := timePositive.trans timeAbove
  have positiveLower : frequency / 4 * time ≤ ‖separatingPositive frequency frequencyPositive time‖ := by
    simpa only [separatingEscapeCoordinate, separatingPositive_norm] using coordinateLower time timeAbove.le
  have negativeLower : (Real.sqrt 2 - 1) * (frequency / 4 * time) ≤
      ‖separatingNegative frequency frequencyPositive time‖ :=
    (mul_le_mul_of_nonneg_left positiveLower minimumPositive.le).trans
      (separating_large_norm_lower frequency frequencyPositive time).1
  have numeratorBound : frequency * ‖separatingDipoleSeparation frequency frequencyPositive time‖ ≤ frequency * 2 :=
    mul_le_mul_of_nonneg_left (separatingDipoleSeparation_norm_bounds frequency frequencyPositive time).2 frequencyPositive.le
  have denominatorBound : 4 * (frequency / 4 * time) * ((Real.sqrt 2 - 1) * (frequency / 4 * time)) ≤
      4 * ‖separatingPositive frequency frequencyPositive time‖ * ‖separatingNegative frequency frequencyPositive time‖ := by
    gcongr
  simp only [norm_div, norm_mul, Complex.norm_I, one_mul, norm_star,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyPositive]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ frequency * 2 / (4 * (frequency / 4 * time) *
      ((Real.sqrt 2 - 1) * (frequency / 4 * time))) := by
      apply div_le_div₀ (by positivity) numeratorBound (by positivity) denominatorBound
    _ = _ := by field_simp; ring

theorem separatingDipoleCenter_scattering (frequency : ℝ) (frequencyPositive : 0 < frequency)
    {limit : ℂ} (limitNorm : ‖limit‖ = 1) {separationBound separationTime : ℝ}
    (boundPositive : 0 < separationBound) (timePositive : 0 < separationTime)
    (separationError : ∀ time, separationTime < time →
      ‖separatingDipoleSeparation frequency frequencyPositive time - limit‖ ≤ separationBound / time ^ 2) :
    ∃ offset : ℂ, ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ), ∀ time, timeMin < time →
      ‖separatingDipoleCenter frequency frequencyPositive time +
        (Complex.I * (frequency : ℂ) / star limit) * (time : ℂ) - offset‖ ≤ bound / time := by
  obtain ⟨remainderBound, remainderPositive, remainderTime, remainderTimePositive, remainderError⟩ :=
    separatingDipoleCenter_remainder_decay frequency frequencyPositive
  have thresholdPositive : 0 < max separationTime remainderTime :=
    lt_of_lt_of_le timePositive (le_max_left _ _)
  have derivative : ∀ time : ℝ, HasDerivAt
      (fun currentTime => separatingDipoleCenter frequency frequencyPositive currentTime +
        (Complex.I * (frequency : ℂ) / star limit) * (currentTime : ℂ))
      (Complex.I * (frequency : ℂ) * ((star limit)⁻¹ -
        (star (separatingDipoleSeparation frequency frequencyPositive time))⁻¹) +
        Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) /
          (4 * star (separatingPositive frequency frequencyPositive time) *
            star (separatingNegative frequency frequencyPositive time))) time := by
    intro time
    convert (separatingDipoleCenter_hasDerivAt frequency frequencyPositive time).add
      ((hasDerivAt_id time).ofReal_comp.const_mul (Complex.I * (frequency : ℂ) / star limit)) using 1
    simp only [id_eq, Complex.ofReal_one, mul_one, div_eq_mul_inv]
    ring
  have decay : ∀ time : ℝ, max separationTime remainderTime < time →
      ‖Complex.I * (frequency : ℂ) * ((star limit)⁻¹ -
        (star (separatingDipoleSeparation frequency frequencyPositive time))⁻¹) +
        Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) /
          (4 * star (separatingPositive frequency frequencyPositive time) *
            star (separatingNegative frequency frequencyPositive time))‖ ≤
        (frequency * separationBound + remainderBound) / time ^ 2 := by
    intro time timeAbove
    have separationTimeAbove := lt_of_le_of_lt (le_max_left separationTime remainderTime) timeAbove
    have remainderTimeAbove := lt_of_le_of_lt (le_max_right separationTime remainderTime) timeAbove
    have inverseBound : ‖(star limit)⁻¹ - (star (separatingDipoleSeparation frequency frequencyPositive time))⁻¹‖ ≤
        ‖separatingDipoleSeparation frequency frequencyPositive time - limit‖ := by
      calc
        _ ≤ ‖star limit - star (separatingDipoleSeparation frequency frequencyPositive time)‖ :=
          complex_inverse_difference_le (by rw [norm_star, limitNorm])
            (by simpa only [norm_star] using (separatingDipoleSeparation_norm_bounds frequency frequencyPositive time).1)
        _ = _ := by rw [← star_sub, norm_star, norm_sub_rev]
    calc
      _ ≤ ‖Complex.I * (frequency : ℂ) * ((star limit)⁻¹ -
          (star (separatingDipoleSeparation frequency frequencyPositive time))⁻¹)‖ +
        ‖Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) /
          (4 * star (separatingPositive frequency frequencyPositive time) *
            star (separatingNegative frequency frequencyPositive time))‖ := norm_add_le _ _
      _ ≤ frequency * (separationBound / time ^ 2) + remainderBound / time ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos frequencyPositive]
        exact add_le_add (mul_le_mul_of_nonneg_left
          (inverseBound.trans (separationError time separationTimeAbove)) frequencyPositive.le)
          (remainderError time remainderTimeAbove)
      _ = _ := by ring
  obtain ⟨offset, _, errorProperty⟩ := complex_atTop_linear_error thresholdPositive
    (show 0 ≤ frequency * separationBound + remainderBound by positivity)
    (fun time _ => derivative time) decay
  exact ⟨offset, frequency * separationBound + remainderBound, by positivity,
    max separationTime remainderTime, thresholdPositive, errorProperty⟩

theorem separating_scattering_asymptotics (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ angle : ℝ, ∃ offset : ℂ, ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ), ∀ time, timeMin ≤ time →
      ‖separatingPositive frequency frequencyPositive time + separatingNegative frequency frequencyPositive time -
        Complex.exp (Complex.I * (angle : ℂ))‖ ≤ bound / time ^ 2 ∧
      ‖(separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time) / 2 +
        Complex.I * (frequency : ℂ) * Complex.exp (Complex.I * (angle : ℂ)) * (time : ℂ) - offset‖ ≤ bound / time := by
  obtain ⟨limit, limitNorm, _, separationBound, separationPositive, separationTime, separationTimePositive, separationError⟩ :=
    separatingDipoleSeparation_scattering frequency frequencyPositive
  obtain ⟨offset, centerBound, centerPositive, centerTime, centerTimePositive, centerError⟩ :=
    separatingDipoleCenter_scattering frequency frequencyPositive limitNorm separationPositive separationTimePositive separationError
  have representation : Complex.exp (Complex.I * (Complex.arg limit : ℂ)) = limit := by
    simpa only [limitNorm, Complex.ofReal_one, one_mul, mul_one, mul_comm] using Complex.norm_mul_exp_arg_mul_I limit
  have limitNonzero : limit ≠ 0 := norm_ne_zero_iff.mp (by rw [limitNorm]; norm_num)
  have product : limit * star limit = 1 := by
    simpa only [Complex.star_def, limitNorm, one_pow, Complex.ofReal_one] using Complex.mul_conj' limit
  have coefficient : Complex.I * (frequency : ℂ) / star limit = Complex.I * (frequency : ℂ) * limit := by
    apply (div_eq_iff (star_ne_zero.mpr limitNonzero)).mpr
    rw [mul_assoc, product, mul_one]
  refine ⟨Complex.arg limit, offset, max separationBound centerBound,
    lt_of_lt_of_le separationPositive (le_max_left _ _), max separationTime centerTime + 1,
    by linarith [le_max_left separationTime centerTime], ?_⟩
  intro time timeAbove
  have separationTimeAbove : separationTime < time := by linarith [le_max_left separationTime centerTime]
  have centerTimeAbove : centerTime < time := by linarith [le_max_right separationTime centerTime]
  have timePositive : 0 < time := separationTimePositive.trans separationTimeAbove
  rw [representation]
  constructor
  · exact (separationError time separationTimeAbove).trans
      (div_le_div_of_nonneg_right (le_max_left separationBound centerBound) (sq_nonneg time))
  · have result := centerError time centerTimeAbove
    rw [coefficient] at result
    exact result.trans (div_le_div_of_nonneg_right (le_max_right separationBound centerBound) timePositive.le)

end EulerNonuniqueness.Section2

