import EulerNonuniqueness.Section6.PairedStrainRemainder
import EulerNonuniqueness.Section6.DipoleQuadraticMoment

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointCauchyField (positions : FourPointConfiguration) (location : ℂ) : ℂ :=
  ∑ target : Fin 4, (fourPointSign target : ℂ) / (location - positions target)

def fourPointCauchyStrain (positions : FourPointConfiguration) (location : ℂ) : ℂ :=
  -∑ target : Fin 4, (fourPointSign target : ℂ) / (location - positions target) ^ 2

theorem fourPointCauchyField_hasDerivAt (positions : FourPointConfiguration) {location : ℂ}
    (noncollision : ∀ target, location - positions target ≠ 0) :
    HasDerivAt (fourPointCauchyField positions) (fourPointCauchyStrain positions location) location := by
  have derivative (target : Fin 4) : HasDerivAt
      (fun current : ℂ => (fourPointSign target : ℂ) / (current - positions target))
      (-(fourPointSign target : ℂ) / (location - positions target) ^ 2) location := by
    simpa only [zero_mul, mul_one, zero_sub] using
      (hasDerivAt_const location (fourPointSign target : ℂ)).div
        ((hasDerivAt_id location).sub_const (positions target)) (noncollision target)
  simpa only [fourPointCauchyField, fourPointCauchyStrain, neg_div, Finset.sum_neg_distrib] using
    HasDerivAt.sum (u := Finset.univ) (fun target _ => derivative target)

theorem cauchyStrainTaylorRemainder_scaled {location source : ℂ}
    (locationNonzero : location ≠ 0) (differenceNonzero : location - source ≠ 0) :
    cauchyStrainTaylorRemainder (source / location) / location ^ 2 =
      1 / (location - source) ^ 2 - 1 / location ^ 2 - 2 * source / location ^ 3 - 3 * source ^ 2 / location ^ 4 := by
  have identity : 1 - source / location = (location - source) / location := by
    field_simp
  unfold cauchyStrainTaylorRemainder
  rw [identity]
  field_simp [locationNonzero, differenceNonzero]
  ring

set_option maxHeartbeats 1000000 in
theorem fourPointCauchyStrain_moment_identity {positions : FourPointConfiguration} {center location : ℂ}
    (locationNonzero : location - center ≠ 0) (noncollision : ∀ target, location - positions target ≠ 0) :
    fourPointCauchyStrain positions location +
      2 * fourPointSignedMoment positions / (location - center) ^ 3 +
      3 * (∑ target : Fin 4, (fourPointSign target : ℂ) * (positions target - center) ^ 2) /
        (location - center) ^ 4 =
      -(∑ target : Fin 4, (fourPointSign target : ℂ) *
        cauchyStrainTaylorRemainder ((positions target - center) / (location - center))) / (location - center) ^ 2 := by
  have scaled (target : Fin 4) := cauchyStrainTaylorRemainder_scaled locationNonzero
    (show location - center - (positions target - center) ≠ 0 by simpa only [sub_sub_sub_cancel_right] using noncollision target)
  simp only [sub_sub_sub_cancel_right] at scaled
  simp [fourPointCauchyStrain, fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ]
  have first := scaled 0
  have second := scaled 1
  have third := scaled 2
  have fourth := scaled 3
  linear_combination first + second - third - fourth

theorem twoDipole_CauchyStrain_paired_remainder
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (locationNonzero : location - (firstCenter + secondCenter) / 2 ≠ 0)
    (radiusSmall : radius ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2)
    (inside : ∀ target, ‖twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target -
      (firstCenter + secondCenter) / 2‖ ≤ radius) :
    ‖fourPointCauchyStrain (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location +
      2 * (firstSeparation + secondSeparation) / (location - (firstCenter + secondCenter) / 2) ^ 3 +
      3 * ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)) /
        (location - (firstCenter + secondCenter) / 2) ^ 4‖ ≤
      176 * radius ^ 2 * (‖firstSeparation‖ + ‖secondSeparation‖) /
        ‖location - (firstCenter + secondCenter) / 2‖ ^ 5 := by
  let center := (firstCenter + secondCenter) / 2
  let positions := twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation
  let displacement := location - center
  have distancePositive : 0 < ‖displacement‖ := norm_pos_iff.mpr locationNonzero
  have normalizedRadius : radius / ‖displacement‖ ≤ 1 / 2 :=
    (div_le_iff₀ distancePositive).mpr (by dsimp [displacement, center]; linarith)
  have normalizedInside (target : Fin 4) : ‖(positions target - center) / displacement‖ ≤ radius / ‖displacement‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right (inside target) distancePositive.le
  have collisionFree (target : Fin 4) : location - positions target ≠ 0 := by
    intro zero
    have equality : location = positions target := sub_eq_zero.mp zero
    have estimate := inside target
    change ‖positions target - center‖ ≤ radius at estimate
    rw [← equality] at estimate
    change ‖displacement‖ ≤ radius at estimate
    dsimp [displacement, center] at distancePositive
    linarith
  have arithmeticCenter : fourPointArithmeticCenter positions = center := by
    dsimp [positions, center]
    simp [fourPointArithmeticCenter, twoDipoleConfiguration, Fin.sum_univ_succ]
    ring
  have momentIdentity := fourPointCauchyStrain_moment_identity locationNonzero collisionFree
  rw [twoDipole_signed_moment] at momentIdentity
  have secondMoment : (∑ target : Fin 4, (fourPointSign target : ℂ) * (positions target - center) ^ 2) =
      (firstCenter - secondCenter) * (firstSeparation - secondSeparation) := by
    rw [← arithmeticCenter]
    exact twoDipole_centered_complex_moment _ _ _ _
  rw [secondMoment] at momentIdentity
  rw [momentIdentity, norm_div, norm_neg, norm_pow]
  have firstPair := cauchyStrainTaylorRemainder_pair_bound (div_nonneg radiusNonnegative distancePositive.le)
    normalizedRadius (normalizedInside 0) (normalizedInside 2)
  have secondPair := cauchyStrainTaylorRemainder_pair_bound (div_nonneg radiusNonnegative distancePositive.le)
    normalizedRadius (normalizedInside 1) (normalizedInside 3)
  have firstDifference : (positions 0 - center) / displacement - (positions 2 - center) / displacement =
      firstSeparation / displacement := by dsimp [positions]; simp [twoDipoleConfiguration]; ring
  have secondDifference : (positions 1 - center) / displacement - (positions 3 - center) / displacement =
      secondSeparation / displacement := by dsimp [positions]; simp [twoDipoleConfiguration]; ring
  rw [firstDifference, norm_div] at firstPair
  rw [secondDifference, norm_div] at secondPair
  have sumIdentity : (∑ target : Fin 4, (fourPointSign target : ℂ) *
      cauchyStrainTaylorRemainder ((positions target - center) / displacement)) =
      (cauchyStrainTaylorRemainder ((positions 0 - center) / displacement) -
        cauchyStrainTaylorRemainder ((positions 2 - center) / displacement)) +
      (cauchyStrainTaylorRemainder ((positions 1 - center) / displacement) -
        cauchyStrainTaylorRemainder ((positions 3 - center) / displacement)) := by
    simp [fourPointSign, Fin.sum_univ_succ]
    ring
  change ‖∑ target : Fin 4, (fourPointSign target : ℂ) *
      cauchyStrainTaylorRemainder ((positions target - center) / displacement)‖ / ‖displacement‖ ^ 2 ≤ _
  rw [sumIdentity]
  calc
    _ ≤ (176 * (radius / ‖displacement‖) ^ 2 * (‖firstSeparation‖ / ‖displacement‖) +
        176 * (radius / ‖displacement‖) ^ 2 * (‖secondSeparation‖ / ‖displacement‖)) / ‖displacement‖ ^ 2 :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add firstPair secondPair)) (sq_nonneg _)
    _ = _ := by
      change _ = 176 * radius ^ 2 * (‖firstSeparation‖ + ‖secondSeparation‖) / ‖displacement‖ ^ 5
      field_simp
      ring

theorem twoDipole_CauchyStrain_far_field
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖fourPointCauchyStrain (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location +
      2 * (firstSeparation + secondSeparation) / (location - (firstCenter + secondCenter) / 2) ^ 3 +
      3 * ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)) /
        (location - (firstCenter + secondCenter) / 2) ^ 4‖ ≤
      704 * ‖firstCenter - secondCenter‖ ^ 2 * length /
        ‖location - (firstCenter + secondCenter) / 2‖ ^ 5 := by
  have distancePositive : 0 < ‖location - (firstCenter + secondCenter) / 2‖ := by nlinarith
  have estimate := twoDipole_CauchyStrain_paired_remainder (norm_nonneg (firstCenter - secondCenter))
    (norm_pos_iff.mp distancePositive) far (fun target => by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using
        twoDipole_mem_center_ball (firstBound.trans (by linarith)) (secondBound.trans (by linarith)) target)
  apply estimate.trans
  have separationSum : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ 4 * length := by linarith
  calc
    _ ≤ 176 * ‖firstCenter - secondCenter‖ ^ 2 * (4 * length) /
        ‖location - (firstCenter + secondCenter) / 2‖ ^ 5 := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.Section6
