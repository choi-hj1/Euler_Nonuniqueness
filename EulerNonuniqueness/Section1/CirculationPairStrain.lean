import EulerNonuniqueness.Section1.IndividualCirculationStrain

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.circulation_le_strain_location_sq (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (index : ℕ) :
    scales.circulation (index + 1) ≤ scales.strain * scales.location (index + 1) ^ 2 := by
  have individual := (scales.circulation_location_summable frequencyBound ratioBound alphaPositive 2).le_tsum
    index (fun source _ => div_nonneg
      (scales.circulation_pos (zero_lt_one.trans_le frequencyBound) (by linarith) _).le (sq_nonneg _))
  exact (div_le_iff₀ (sq_pos_of_pos (scales.location_pos (index + 1)))).mp individual

theorem Scales.circulation_pair_le_strain_distance_sq (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (first second : ℕ) (different : first ≠ second) :
    scales.circulation (first + 1) + scales.circulation (second + 1) ≤
      9 * scales.strain * |scales.location (first + 1) - scales.location (second + 1)| ^ 2 := by
  have firstBound := scales.circulation_le_strain_location_sq frequencyBound ratioBound alphaPositive first
  have secondBound := scales.circulation_le_strain_location_sq frequencyBound ratioBound alphaPositive second
  have locations := scales.location_sum_le_three_distance
    (show first + 1 ≠ second + 1 from fun equality => different (Nat.add_right_cancel equality))
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos (zero_lt_one.trans_le frequencyBound) (by linarith) _).le (sq_nonneg _)
  have squares : scales.location (first + 1) ^ 2 + scales.location (second + 1) ^ 2 ≤
      9 * |scales.location (first + 1) - scales.location (second + 1)| ^ 2 := by
    have product := mul_nonneg (scales.location_pos (first + 1)).le (scales.location_pos (second + 1)).le
    have squareBound := (sq_le_sq₀
      (add_nonneg (scales.location_pos (first + 1)).le (scales.location_pos (second + 1)).le)
      (by positivity : 0 ≤ 3 * |scales.location (first + 1) - scales.location (second + 1)|)).mpr locations
    nlinarith
  calc
    _ ≤ scales.strain * scales.location (first + 1) ^ 2 + scales.strain * scales.location (second + 1) ^ 2 :=
      add_le_add firstBound secondBound
    _ = scales.strain * (scales.location (first + 1) ^ 2 + scales.location (second + 1) ^ 2) := by ring
    _ ≤ scales.strain * (9 * |scales.location (first + 1) - scales.location (second + 1)| ^ 2) :=
      mul_le_mul_of_nonneg_left squares strainNonnegative
    _ = _ := by ring

end EulerNonuniqueness.Paper
