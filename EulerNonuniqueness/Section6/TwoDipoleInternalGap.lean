import EulerNonuniqueness.Section6.TwoDipoleDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

theorem separated_cluster_points_gap {firstCenter secondCenter firstOffset secondOffset : ℂ}
    {length : ℝ} (lengthNonnegative : 0 ≤ length)
    (centers : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (firstSmall : ‖firstOffset‖ ≤ length) (secondSmall : ‖secondOffset‖ ≤ length) :
    2 * length ≤ ‖(firstCenter + firstOffset) - (secondCenter + secondOffset)‖ := by
  have first := norm_sub_le_norm_sub_add_norm_sub firstCenter (firstCenter + firstOffset) secondCenter
  have second := norm_sub_le_norm_sub_add_norm_sub (firstCenter + firstOffset)
    (secondCenter + secondOffset) secondCenter
  have firstIdentity : firstCenter - (firstCenter + firstOffset) = -firstOffset := by abel
  have secondIdentity : secondCenter + secondOffset - secondCenter = secondOffset := by abel
  rw [firstIdentity, norm_neg] at first
  rw [secondIdentity] at second
  linarith

theorem twoDipoleConfiguration_internal_gap {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    {length : ℝ} (lengthNonnegative : 0 ≤ length)
    (centers : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (firstLower : length / 2 ≤ ‖firstSeparation‖) (secondLower : length / 2 ≤ ‖secondSeparation‖)
    (firstUpper : ‖firstSeparation‖ ≤ 2 * length) (secondUpper : ‖secondSeparation‖ ≤ 2 * length)
    (target source : Fin 4) (different : target ≠ source) :
    length / 2 ≤ ‖twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target -
      twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation source‖ := by
  have firstHalf : ‖firstSeparation / 2‖ ≤ length := by
    rw [norm_div, Complex.norm_ofNat]
    linarith
  have secondHalf : ‖secondSeparation / 2‖ ≤ length := by
    rw [norm_div, Complex.norm_ofNat]
    linarith
  have cross (firstSign secondSign : ℂ) (firstNorm : ‖firstSign‖ = 1) (secondNorm : ‖secondSign‖ = 1) :
      length / 2 ≤ ‖(firstCenter + firstSign * (firstSeparation / 2)) -
        (secondCenter + secondSign * (secondSeparation / 2))‖ := by
    have actual := separated_cluster_points_gap lengthNonnegative centers
      (show ‖firstSign * (firstSeparation / 2)‖ ≤ length by simpa [norm_mul, firstNorm] using firstHalf)
      (show ‖secondSign * (secondSeparation / 2)‖ ≤ length by simpa [norm_mul, secondNorm] using secondHalf)
    linarith
  have crossPP := cross 1 1 (by simp) (by simp)
  have crossPN := cross 1 (-1) (by simp) (by simp)
  have crossNP := cross (-1) 1 (by simp) (by simp)
  have crossNN := cross (-1) (-1) (by simp) (by simp)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at crossPP crossPN crossNP crossNN
  fin_cases target <;> fin_cases source <;>
    simp only [Fin.isValue, ne_eq, not_true_eq_false] at different
  all_goals simp [twoDipoleConfiguration]
  all_goals solve
    | exact crossPP
    | exact crossPN
    | exact crossNP
    | exact crossNN
    | simpa only [norm_sub_rev] using crossPP
    | simpa only [norm_sub_rev] using crossPN
    | simpa only [norm_sub_rev] using crossNP
    | simpa only [norm_sub_rev] using crossNN
    | convert firstLower using 1 <;> congr 1 <;> ring
    | convert secondLower using 1 <;> congr 1 <;> ring
    | rw [norm_sub_rev]; convert firstLower using 1 <;> congr 1 <;> ring
    | rw [norm_sub_rev]; convert secondLower using 1 <;> congr 1 <;> ring
    | have identity : firstCenter - firstSeparation / 2 - (firstCenter + firstSeparation / 2) = -firstSeparation := by ring
      rw [identity, norm_neg]
      exact firstLower
    | have identity : secondCenter - secondSeparation / 2 - (secondCenter + secondSeparation / 2) = -secondSeparation := by ring
      rw [identity, norm_neg]
      exact secondLower

end EulerNonuniqueness.Section6
