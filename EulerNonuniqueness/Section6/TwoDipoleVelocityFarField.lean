import EulerNonuniqueness.Section6.PairedPhysicalStrain

noncomputable section

namespace EulerNonuniqueness.Section6

theorem inverse_linear_remainder_pair_bound {displacement first second : ℂ} {radius : ℝ}
    (distancePositive : 0 < ‖displacement‖) (radiusNonnegative : 0 ≤ radius)
    (radiusSmall : radius ≤ ‖displacement‖ / 2)
    (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius) :
    ‖((1 / (displacement - first) - 1 / displacement - first / displacement ^ 2) -
      (1 / (displacement - second) - 1 / displacement - second / displacement ^ 2))‖ ≤
      10 * radius * ‖first - second‖ / ‖displacement‖ ^ 3 := by
  have firstGap : ‖displacement‖ / 2 ≤ ‖displacement - first‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub displacement first 0
    simp only [sub_zero] at triangle
    linarith
  have secondGap : ‖displacement‖ / 2 ≤ ‖displacement - second‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub displacement second 0
    simp only [sub_zero] at triangle
    linarith
  have displacementNonzero := norm_pos_iff.mp distancePositive
  have firstNonzero := norm_pos_iff.mp ((half_pos distancePositive).trans_le firstGap)
  have secondNonzero := norm_pos_iff.mp ((half_pos distancePositive).trans_le secondGap)
  have identity :
      (1 / (displacement - first) - 1 / displacement - first / displacement ^ 2) -
        (1 / (displacement - second) - 1 / displacement - second / displacement ^ 2) =
      (first - second) * (displacement * (first + second) - first * second) /
        (displacement ^ 2 * (displacement - first) * (displacement - second)) := by
    field_simp [displacementNonzero, firstNonzero, secondNonzero]
    ring
  have numerator : ‖displacement * (first + second) - first * second‖ ≤
      (5 / 2 : ℝ) * ‖displacement‖ * radius := by
    have triangle := norm_sub_le (displacement * (first + second)) (first * second)
    rw [norm_mul, norm_mul] at triangle
    have sumBound := (norm_add_le first second).trans (add_le_add firstBound secondBound)
    have productBound := mul_le_mul firstBound secondBound (norm_nonneg second) radiusNonnegative
    have linearBound := mul_le_mul_of_nonneg_left sumBound (norm_nonneg displacement)
    nlinarith
  rw [identity, norm_div, norm_mul, norm_mul, norm_mul, norm_pow]
  have denominatorPositive : 0 < ‖displacement‖ ^ 2 * ‖displacement - first‖ * ‖displacement - second‖ := by positivity
  apply (div_le_iff₀ denominatorPositive).mpr
  have denominatorBound : ‖displacement‖ ^ 2 * (‖displacement‖ / 2) * (‖displacement‖ / 2) ≤
      ‖displacement‖ ^ 2 * ‖displacement - first‖ * ‖displacement - second‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left firstGap (sq_nonneg _)) secondGap
      (half_pos distancePositive).le (by positivity)
  have multiplied := mul_le_mul_of_nonneg_left denominatorBound
    (show 0 ≤ 10 * radius * ‖first - second‖ / ‖displacement‖ ^ 3 by positivity)
  have cancellation : (10 * radius * ‖first - second‖ / ‖displacement‖ ^ 3) *
      (‖displacement‖ ^ 2 * (‖displacement‖ / 2) * (‖displacement‖ / 2)) =
      ‖first - second‖ * ((5 / 2 : ℝ) * ‖displacement‖ * radius) := by
    field_simp
    ring
  rw [cancellation] at multiplied
  exact (mul_le_mul_of_nonneg_left numerator (norm_nonneg _)).trans multiplied

theorem twoDipole_CauchyVelocity_far_field
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖fourPointCauchyField (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location -
      (firstSeparation + secondSeparation) / (location - (firstCenter + secondCenter) / 2) ^ 2‖ ≤
      40 * length * ‖firstCenter - secondCenter‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 3 := by
  let center := (firstCenter + secondCenter) / 2
  let displacement := location - center
  let radius := ‖firstCenter - secondCenter‖
  let positions := twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation
  have radiusPositive : 0 < radius := by dsimp only [radius]; linarith
  have distancePositive : 0 < ‖displacement‖ := by dsimp only [displacement, center]; linarith
  have offsets (target : Fin 4) : ‖positions target - center‖ ≤ radius := by
    have firstCenterBound : ‖firstCenter - center‖ = radius / 2 := by
      have identity : firstCenter - center = (firstCenter - secondCenter) / 2 := by dsimp only [center]; ring
      rw [identity, norm_div]
      norm_num
      rfl
    have secondCenterBound : ‖secondCenter - center‖ = radius / 2 := by
      have identity : secondCenter - center = -(firstCenter - secondCenter) / 2 := by dsimp only [center]; ring
      rw [identity, norm_div, norm_neg]
      norm_num
      rfl
    have firstHalf : ‖firstSeparation / 2‖ ≤ length := by rw [norm_div]; norm_num; linarith
    have secondHalf : ‖secondSeparation / 2‖ ≤ length := by rw [norm_div]; norm_num; linarith
    have addBound (point shift : ℂ) (centerBound : ‖point - center‖ = radius / 2) (shiftBound : ‖shift‖ ≤ length) :
        ‖point + shift - center‖ ≤ radius := by
      have triangle := norm_add_le (point - center) shift
      have identity : point + shift - center = (point - center) + shift := by ring
      rw [identity]
      rw [centerBound] at triangle
      dsimp only [radius] at triangle ⊢
      linarith
    fin_cases target
    · exact addBound firstCenter _ firstCenterBound firstHalf
    · exact addBound secondCenter _ secondCenterBound secondHalf
    · simpa only [sub_eq_add_neg, neg_div, norm_neg] using addBound firstCenter (-(firstSeparation / 2)) firstCenterBound (by simpa only [norm_neg] using firstHalf)
    · simpa only [sub_eq_add_neg, neg_div, norm_neg] using addBound secondCenter (-(secondSeparation / 2)) secondCenterBound (by simpa only [norm_neg] using secondHalf)
  let remainder := fun position : ℂ => 1 / (displacement - position) - 1 / displacement - position / displacement ^ 2
  have firstPair := inverse_linear_remainder_pair_bound distancePositive radiusPositive.le far (offsets 0) (offsets 2)
  have secondPair := inverse_linear_remainder_pair_bound distancePositive radiusPositive.le far (offsets 1) (offsets 3)
  have firstDifference : (positions 0 - center) - (positions 2 - center) = firstSeparation := by
    dsimp only [positions, twoDipoleConfiguration]
    simp
  have secondDifference : (positions 1 - center) - (positions 3 - center) = secondSeparation := by
    dsimp only [positions, twoDipoleConfiguration]
    simp
  rw [firstDifference] at firstPair
  rw [secondDifference] at secondPair
  have identity : fourPointCauchyField positions location - (firstSeparation + secondSeparation) / displacement ^ 2 =
      (remainder (positions 0 - center) - remainder (positions 2 - center)) +
        (remainder (positions 1 - center) - remainder (positions 3 - center)) := by
    dsimp only [remainder, displacement, positions, fourPointCauchyField]
    simp [fourPointSign, twoDipoleConfiguration, Fin.sum_univ_succ]
    ring
  rw [identity]
  apply (norm_add_le _ _).trans ((add_le_add firstPair secondPair).trans ?_)
  have firstWeighted := mul_le_mul_of_nonneg_left firstBound (show 0 ≤ 10 * radius / ‖displacement‖ ^ 3 by positivity)
  have secondWeighted := mul_le_mul_of_nonneg_left secondBound (show 0 ≤ 10 * radius / ‖displacement‖ ^ 3 by positivity)
  dsimp only [radius, displacement, center] at firstWeighted secondWeighted ⊢
  convert add_le_add firstWeighted secondWeighted using 1 <;> ring

theorem twoDipole_physical_velocity_far_field_bound (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖fourPointExternalPointVelocity coefficient
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location‖ ≤
      40 * |coefficient| * (‖firstSeparation + secondSeparation‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 2 +
        length * ‖firstCenter - secondCenter‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 3) := by
  have remainder := twoDipole_CauchyVelocity_far_field lengthPositive firstBound secondBound separated far
  let field := fourPointCauchyField (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location
  let leading := (firstSeparation + secondSeparation) / (location - (firstCenter + secondCenter) / 2) ^ 2
  have triangle := norm_sub_le_norm_sub_add_norm_sub field leading 0
  simp only [sub_zero] at triangle
  have fieldBound := triangle.trans (add_le_add remainder (le_refl ‖leading‖))
  dsimp only [leading] at fieldBound
  rw [norm_div, norm_pow] at fieldBound
  rw [fourPointExternalPointVelocity, norm_mul, norm_mul, norm_star, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have multiplied := mul_le_mul_of_nonneg_left fieldBound (abs_nonneg coefficient)
  dsimp only [field] at multiplied
  apply multiplied.trans
  have leadingNonnegative : 0 ≤ ‖firstSeparation + secondSeparation‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 2 := by positivity
  have scalar : ‖firstSeparation + secondSeparation‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 2 +
      40 * (length * ‖firstCenter - secondCenter‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 3) ≤
      40 * (‖firstSeparation + secondSeparation‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 2 +
        length * ‖firstCenter - secondCenter‖ / ‖location - (firstCenter + secondCenter) / 2‖ ^ 3) := by linarith
  convert mul_le_mul_of_nonneg_left scalar (abs_nonneg coefficient) using 1 <;> ring

end EulerNonuniqueness.Section6
