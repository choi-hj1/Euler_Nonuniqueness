import EulerNonuniqueness.Section5.CascadeForeignMomentBound
import EulerNonuniqueness.Section1.CirculationPairStrain

noncomputable section

namespace EulerNonuniqueness.Paper

theorem cascadeForeignDistance_symm {count : ℕ} (scales : Scales) (factor : ℝ) (first second : Fin count) :
    cascadeForeignDistance scales factor first second = cascadeForeignDistance scales factor second first := by
  unfold cascadeForeignDistance
  rw [abs_sub_comm]

theorem cascadeForeignDistance_ge_source {count : ℕ} (scales : Scales) {factor : ℝ}
    (factorPositive : 0 < factor) (first second : Fin count) (different : first ≠ second) :
    factor * scales.location (second.val + 1) / 24 ≤ cascadeForeignDistance scales factor first second := by
  have locations := scales.location_sum_le_three_distance
    (show first.val + 1 ≠ second.val + 1 from fun equal => different (Fin.ext (Nat.add_right_cancel equal)))
  have weighted := mul_le_mul_of_nonneg_left locations factorPositive.le
  have other := mul_pos factorPositive (scales.location_pos (first.val + 1))
  unfold cascadeForeignDistance
  nlinarith

theorem Scales.cascade_cross_source_velocity_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {factor : ℝ} (factorPositive : 0 < factor) (first second : Fin count) (different : first ≠ second) :
    2 * scales.circulation (second.val + 1) / (Real.pi * cascadeForeignDistance scales factor first second) +
      2 * scales.circulation (first.val + 1) / (Real.pi * cascadeForeignDistance scales factor first second) ≤
        (144 / (Real.pi * factor)) * scales.strain *
          |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have valuesDifferent : first.val + 1 ≠ second.val + 1 :=
    fun equal => different (Fin.ext (Nat.add_right_cancel equal))
  have locations := scales.location_sum_le_three_distance valuesDifferent
  have gapPositive := scales.location_distance_pos valuesDifferent
  have firstPositive := scales.location_pos (first.val + 1)
  have secondPositive := scales.location_pos (second.val + 1)
  have squareSum : scales.location (first.val + 1) ^ 2 + scales.location (second.val + 1) ^ 2 ≤
      9 * |scales.location (first.val + 1) - scales.location (second.val + 1)| ^ 2 := by
    have sumSquare := pow_le_pow_left₀ (by positivity : 0 ≤ scales.location (first.val + 1) + scales.location (second.val + 1))
      locations 2
    nlinarith
  have masses := add_le_add
    (scales.circulation_le_strain_location_sq frequencyBound ratioBound alphaPositive first.val)
    (scales.circulation_le_strain_location_sq frequencyBound ratioBound alphaPositive second.val)
  have weighted := mul_le_mul_of_nonneg_left squareSum strainNonnegative
  have massBound : scales.circulation (first.val + 1) + scales.circulation (second.val + 1) ≤
      9 * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)| ^ 2 := by
    nlinarith
  have denominatorPositive : 0 < Real.pi * factor *
      |scales.location (first.val + 1) - scales.location (second.val + 1)| := by positivity
  calc
    _ = 16 * (scales.circulation (first.val + 1) + scales.circulation (second.val + 1)) /
        (Real.pi * factor * |scales.location (first.val + 1) - scales.location (second.val + 1)|) := by
      unfold cascadeForeignDistance
      field_simp [Real.pi_ne_zero, factorPositive.ne', gapPositive.ne']
      <;> ring
    _ ≤ 16 * (9 * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)| ^ 2) /
        (Real.pi * factor * |scales.location (first.val + 1) - scales.location (second.val + 1)|) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left massBound (by norm_num)) denominatorPositive.le
    _ = _ := by
      generalize |scales.location (first.val + 1) - scales.location (second.val + 1)| = separation at gapPositive ⊢
      field_simp [Real.pi_ne_zero, factorPositive.ne', gapPositive.ne']
      <;> ring

end EulerNonuniqueness.Paper
