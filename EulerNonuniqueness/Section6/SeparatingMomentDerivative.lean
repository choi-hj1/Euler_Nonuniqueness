import EulerNonuniqueness.Section6.SeparatingMoment

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem separatingDipoleCenter_derivative_error (frequency : ℝ) (frequencyPositive : 0 < frequency)
    {limit : ℂ} (limitNorm : ‖limit‖ = 1) {separationBound separationTime : ℝ}
    (boundPositive : 0 < separationBound) (timePositive : 0 < separationTime)
    (separationError : ∀ time, separationTime < time →
      ‖separatingDipoleSeparation frequency frequencyPositive time - limit‖ ≤ separationBound / time ^ 2) :
    ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ), ∀ time, timeMin < time →
      ‖deriv (separatingDipoleCenter frequency frequencyPositive) time + Complex.I * (frequency : ℂ) * limit‖ ≤
        bound / time ^ 2 := by
  obtain ⟨remainderBound, remainderPositive, remainderTime, remainderTimePositive, remainderError⟩ :=
    separatingDipoleCenter_remainder_decay frequency frequencyPositive
  have product : limit * star limit = 1 := by
    simpa only [Complex.star_def, limitNorm, one_pow, Complex.ofReal_one] using Complex.mul_conj' limit
  have limitInverse : (star limit)⁻¹ = limit := inv_eq_of_mul_eq_one_left product
  refine ⟨frequency * separationBound + remainderBound, by positivity,
    max separationTime remainderTime, lt_of_lt_of_le timePositive (le_max_left _ _), ?_⟩
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
  have identity : deriv (separatingDipoleCenter frequency frequencyPositive) time +
      Complex.I * (frequency : ℂ) * limit =
      Complex.I * (frequency : ℂ) * ((star limit)⁻¹ -
        (star (separatingDipoleSeparation frequency frequencyPositive time))⁻¹) +
      Complex.I * (frequency : ℂ) * star (separatingDipoleSeparation frequency frequencyPositive time) /
        (4 * star (separatingPositive frequency frequencyPositive time) *
          star (separatingNegative frequency frequencyPositive time)) := by
    rw [(separatingDipoleCenter_hasDerivAt frequency frequencyPositive time).deriv, limitInverse]
    ring
  rw [identity]
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

theorem separating_complex_moment_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency)
    (circulation time : ℝ) :
    HasDerivAt (fun current => quadrupoleComplexMoment circulation
      (separatingPositive frequency frequencyPositive current) (separatingNegative frequency frequencyPositive current))
      (4 * (circulation : ℂ) *
        (deriv (separatingDipoleCenter frequency frequencyPositive) time *
          separatingDipoleSeparation frequency frequencyPositive time +
          separatingDipoleCenter frequency frequencyPositive time *
            deriv (separatingDipoleSeparation frequency frequencyPositive) time)) time := by
  have center := (separatingDipoleCenter_hasDerivAt frequency frequencyPositive time).differentiableAt.hasDerivAt
  have separation := (separatingDipoleSeparation_hasDerivAt frequency frequencyPositive time).differentiableAt.hasDerivAt
  convert (center.mul separation).const_mul (4 * (circulation : ℂ)) using 1
  funext current
  dsimp [quadrupoleComplexMoment, separatingDipoleCenter, separatingDipoleSeparation]
  ring

theorem separating_complex_moment_derivative_growth (frequency : ℝ) (frequencyPositive : 0 < frequency)
    (circulation : ℝ) :
    ∃ limit : ℂ, ‖limit‖ = 1 ∧ ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ),
      ∀ time, timeMin ≤ time →
      ‖deriv (fun current => quadrupoleComplexMoment circulation
          (separatingPositive frequency frequencyPositive current) (separatingNegative frequency frequencyPositive current)) time +
        4 * Complex.I * (circulation : ℂ) * (frequency : ℂ) * limit ^ 2‖ ≤ bound / time ^ 2 := by
  obtain ⟨limit, limitNorm, _, separationBound, separationPositive, separationTime, separationTimePositive, separationError⟩ :=
    separatingDipoleSeparation_scattering frequency frequencyPositive
  obtain ⟨offset, centerBound, centerPositive, centerTime, centerTimePositive, centerError⟩ :=
    separatingDipoleCenter_scattering frequency frequencyPositive limitNorm separationPositive separationTimePositive separationError
  obtain ⟨centerDerivativeBound, centerDerivativePositive, centerDerivativeTime, centerDerivativeTimePositive, centerDerivativeError⟩ :=
    separatingDipoleCenter_derivative_error frequency frequencyPositive limitNorm
      separationPositive separationTimePositive separationError
  obtain ⟨separationDerivativeBound, separationDerivativePositive, separationDerivativeTime, separationDerivativeTimePositive,
    separationDerivativeError⟩ := separatingDipoleSeparation_velocity_decay frequency frequencyPositive
  let centerGrowth := frequency + ‖offset‖ + centerBound
  let bound := 1 + 4 * |circulation| *
    (2 * centerDerivativeBound + frequency * separationBound + centerGrowth * separationDerivativeBound)
  let timeMin := 1 + separationTime + centerTime + centerDerivativeTime + separationDerivativeTime
  refine ⟨limit, limitNorm, bound, by dsimp [bound, centerGrowth]; positivity,
    timeMin, by dsimp [timeMin]; positivity, ?_⟩
  intro time timeAbove
  have separationAbove : separationTime < time := by dsimp [timeMin] at timeAbove; linarith
  have centerAbove : centerTime < time := by dsimp [timeMin] at timeAbove; linarith
  have centerDerivativeAbove : centerDerivativeTime < time := by dsimp [timeMin] at timeAbove; linarith
  have separationDerivativeAbove : separationDerivativeTime < time := by dsimp [timeMin] at timeAbove; linarith
  have timeOne : 1 ≤ time := by dsimp [timeMin] at timeAbove; linarith
  have timePositive : 0 < time := by linarith
  let separation := separatingDipoleSeparation frequency frequencyPositive time
  let center := separatingDipoleCenter frequency frequencyPositive time
  let centerDerivative := deriv (separatingDipoleCenter frequency frequencyPositive) time
  let separationDerivative := deriv (separatingDipoleSeparation frequency frequencyPositive) time
  have separationNorm : ‖separation‖ ≤ 2 :=
    (separatingDipoleSeparation_norm_bounds frequency frequencyPositive time).2
  have separationDerivativeNorm : ‖separationDerivative‖ ≤ separationDerivativeBound / time ^ 3 := by
    rw [show separationDerivative = _ from (separatingDipoleSeparation_hasDerivAt frequency frequencyPositive time).deriv]
    exact separationDerivativeError time separationDerivativeAbove
  have centerNorm : ‖center‖ ≤ centerGrowth * time := by
    have centerError := centerError time centerAbove
    have affineNorm : ‖-Complex.I * (frequency : ℂ) * limit * (time : ℂ) + offset‖ ≤
        frequency * time + ‖offset‖ := by
      convert norm_add_le (-Complex.I * (frequency : ℂ) * limit * (time : ℂ)) offset using 1
      simp [norm_mul, limitNorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos frequencyPositive, abs_of_pos timePositive]
    have coefficient : Complex.I * (frequency : ℂ) / star limit = Complex.I * (frequency : ℂ) * limit := by
      have product : limit * star limit = 1 := by
        simpa only [Complex.star_def, limitNorm, one_pow, Complex.ofReal_one] using Complex.mul_conj' limit
      apply (div_eq_iff (star_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [limitNorm]; norm_num)))).mpr
      rw [mul_assoc, product, mul_one]
    rw [coefficient] at centerError
    have centerComparison : ‖center‖ ≤ centerBound / time + frequency * time + ‖offset‖ := by
      calc
        _ ≤ ‖center - (-Complex.I * (frequency : ℂ) * limit * (time : ℂ) + offset)‖ +
            ‖-Complex.I * (frequency : ℂ) * limit * (time : ℂ) + offset‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            (center - (-Complex.I * (frequency : ℂ) * limit * (time : ℂ) + offset))
            (-Complex.I * (frequency : ℂ) * limit * (time : ℂ) + offset)
        _ ≤ centerBound / time + (frequency * time + ‖offset‖) := by
          apply add_le_add _ affineNorm
          convert centerError using 1
          congr 1
          dsimp [center]
          ring
        _ = _ := by ring
    have divisionBound : centerBound / time ≤ centerBound :=
      (div_le_self centerPositive.le timeOne)
    dsimp [centerGrowth]
    nlinarith [norm_nonneg offset]
  have speedNorm : ‖-Complex.I * (frequency : ℂ) * limit‖ = frequency := by
    simp [norm_mul, limitNorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyPositive]
  have identity : deriv (fun current => quadrupoleComplexMoment circulation
      (separatingPositive frequency frequencyPositive current) (separatingNegative frequency frequencyPositive current)) time +
      4 * Complex.I * (circulation : ℂ) * (frequency : ℂ) * limit ^ 2 =
      4 * (circulation : ℂ) *
        ((centerDerivative + Complex.I * (frequency : ℂ) * limit) * separation +
          (-Complex.I * (frequency : ℂ) * limit) * (separation - limit) + center * separationDerivative) := by
    rw [(separating_complex_moment_hasDerivAt frequency frequencyPositive circulation time).deriv]
    dsimp [centerDerivative, separationDerivative, center, separation]
    ring
  rw [identity, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 4 * |circulation| *
        (‖(centerDerivative + Complex.I * (frequency : ℂ) * limit) * separation‖ +
          ‖(-Complex.I * (frequency : ℂ) * limit) * (separation - limit)‖ + ‖center * separationDerivative‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ = 4 * |circulation| *
        (‖centerDerivative + Complex.I * (frequency : ℂ) * limit‖ * ‖separation‖ +
          frequency * ‖separation - limit‖ + ‖center‖ * ‖separationDerivative‖) := by
      simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, limitNorm, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyPositive]
    _ ≤ 4 * |circulation| *
        ((centerDerivativeBound / time ^ 2) * 2 + frequency * (separationBound / time ^ 2) +
          (centerGrowth * time) * (separationDerivativeBound / time ^ 3)) := by
      gcongr
      · exact centerDerivativeError time centerDerivativeAbove
      · exact separationError time separationAbove
    _ = 4 * |circulation| *
        (2 * centerDerivativeBound + frequency * separationBound + centerGrowth * separationDerivativeBound) / time ^ 2 := by
      field_simp
      ring
    _ ≤ bound / time ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg time)
      dsimp [bound]
      linarith

theorem physical_separating_moment_derivative_growth (length circulation : ℝ)
    (lengthPositive : 0 < length) (circulationPositive : 0 < circulation) :
    let frequency : ℝ := circulation / (2 * Real.pi * length ^ 2)
    let frequencyPositive : 0 < frequency := by dsimp [frequency]; positivity
    ∃ limit : ℂ, ‖limit‖ = 1 ∧ ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ),
      ∀ time, timeMin ≤ time →
      ‖deriv (fun current => quadrupoleComplexMoment circulation
          ((length : ℂ) * separatingPositive frequency frequencyPositive current)
          ((length : ℂ) * separatingNegative frequency frequencyPositive current)) time +
        (2 * Complex.I / (Real.pi : ℂ)) * (circulation : ℂ) ^ 2 * limit ^ 2‖ ≤ bound / time ^ 2 := by
  dsimp only
  have frequencyPositive : 0 < circulation / (2 * Real.pi * length ^ 2) := by positivity
  obtain ⟨limit, limitNorm, bound, boundPositive, timeMin, timePositive, estimate⟩ :=
    separating_complex_moment_derivative_growth (circulation / (2 * Real.pi * length ^ 2)) frequencyPositive
      (circulation * length ^ 2)
  refine ⟨limit, limitNorm, bound, boundPositive, timeMin, timePositive, ?_⟩
  intro time timeAbove
  have functionIdentity :
      (fun current => quadrupoleComplexMoment circulation
        ((length : ℂ) * separatingPositive (circulation / (2 * Real.pi * length ^ 2)) frequencyPositive current)
        ((length : ℂ) * separatingNegative (circulation / (2 * Real.pi * length ^ 2)) frequencyPositive current)) =
      (fun current => quadrupoleComplexMoment (circulation * length ^ 2)
        (separatingPositive (circulation / (2 * Real.pi * length ^ 2)) frequencyPositive current)
        (separatingNegative (circulation / (2 * Real.pi * length ^ 2)) frequencyPositive current)) := by
    funext current
    dsimp [quadrupoleComplexMoment]
    push_cast
    ring
  have coefficientIdentity :
      4 * Complex.I * ((circulation * length ^ 2 : ℝ) : ℂ) *
        ((circulation / (2 * Real.pi * length ^ 2) : ℝ) : ℂ) =
      (2 * Complex.I / (Real.pi : ℂ)) * (circulation : ℂ) ^ 2 := by
    push_cast
    have lengthNonzero : (length : ℂ) ≠ 0 := by exact_mod_cast lengthPositive.ne'
    have piNonzero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [lengthNonzero, piNonzero]
    ring
  rw [functionIdentity]
  rw [coefficientIdentity] at estimate
  exact estimate time timeAbove

end EulerNonuniqueness.Section6
