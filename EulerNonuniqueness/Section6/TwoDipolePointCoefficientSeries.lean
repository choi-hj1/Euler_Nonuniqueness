import EulerNonuniqueness.Section6.PointSourceRelativeSeries
import EulerNonuniqueness.Section6.TwoDipoleDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 200000

theorem twoDipole_pointSourceTaylorCoefficient_summable_and_tsum_le
    (firstCenter secondCenter firstSeparation secondSeparation observation : ℂ) (circulation : ℝ)
    {length receiverRadius distance weight : ℝ}
    (lengthNonnegative : 0 ≤ length) (receiverNonnegative : 0 ≤ receiverRadius)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (firstWidth : ‖firstSeparation‖ ≤ 2 * length) (secondWidth : ‖secondSeparation‖ ≤ 2 * length)
    (pairSeparated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (separated : ‖firstCenter - secondCenter‖ + distance ≤ ‖observation - (firstCenter + secondCenter) / 2‖)
    (small : 4 * weight * receiverRadius / distance < 1) :
    let center := (firstCenter + secondCenter) / 2
    let positions := twoDipoleConfiguration (firstCenter - center) (secondCenter - center) firstSeparation secondSeparation
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius positions (observation - center) power‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius positions (observation - center) power‖) ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖firstSeparation + secondSeparation‖ +
          128 * distance⁻¹ ^ 4 * ‖firstCenter - secondCenter‖ * length)) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  let center := (firstCenter + secondCenter) / 2
  let positions := twoDipoleConfiguration (firstCenter - center) (secondCenter - center) firstSeparation secondSeparation
  let collapsed := twoDipoleConfiguration (firstCenter - center) (secondCenter - center) 0 0
  let radius := ‖firstCenter - secondCenter‖
  have firstCenterNorm : ‖firstCenter - center‖ = radius / 2 := by
    have identity : firstCenter - center = (firstCenter - secondCenter) / 2 := by dsimp only [center]; ring
    rw [identity, norm_div]
    norm_num
    rfl
  have secondCenterNorm : ‖secondCenter - center‖ = radius / 2 := by
    have identity : secondCenter - center = -(firstCenter - secondCenter) / 2 := by dsimp only [center]; ring
    rw [identity, norm_div, norm_neg]
    norm_num
    rfl
  have firstHalf : ‖firstSeparation / 2‖ ≤ length := by rw [norm_div]; norm_num; linarith
  have secondHalf : ‖secondSeparation / 2‖ ≤ length := by rw [norm_div]; norm_num; linarith
  have shiftedBound (point shift : ℂ) (pointNorm : ‖point‖ = radius / 2) (shiftNorm : ‖shift‖ ≤ length) :
      ‖point + shift‖ ≤ radius := by
    have triangle := norm_add_le point shift
    rw [pointNorm] at triangle
    dsimp only [radius] at triangle ⊢
    linarith
  have positionsBound (patch : Fin 4) : ‖positions patch‖ ≤ radius := by
    fin_cases patch
    · exact shiftedBound _ _ firstCenterNorm firstHalf
    · exact shiftedBound _ _ secondCenterNorm secondHalf
    · simpa only [sub_eq_add_neg] using shiftedBound _ (-(firstSeparation / 2)) firstCenterNorm (by simpa only [norm_neg] using firstHalf)
    · simpa only [sub_eq_add_neg] using shiftedBound _ (-(secondSeparation / 2)) secondCenterNorm (by simpa only [norm_neg] using secondHalf)
  have collapsedBound (patch : Fin 4) : ‖collapsed patch‖ ≤ radius := by
    fin_cases patch <;> simp [collapsed, twoDipoleConfiguration, firstCenterNorm, secondCenterNorm]
    all_goals dsimp only [radius]; positivity
  have zeroCoefficient (power : ℕ) : pointSourceTaylorCoefficient circulation receiverRadius collapsed (observation - center) power = 0 := by
    simp [pointSourceTaylorCoefficient, collapsed, twoDipoleConfiguration, fourPointSign, Fin.sum_univ_succ]
  have moment : fourPointSignedMoment positions - fourPointSignedMoment collapsed = firstSeparation + secondSeparation := by
    simp [fourPointSignedMoment, positions, collapsed, twoDipoleConfiguration, fourPointSign, Fin.sum_univ_succ]
    ring
  have differenceSum : (∑ patch : Fin 4, ‖positions patch - collapsed patch‖) ≤ 4 * length := by
    have identity : (∑ patch : Fin 4, ‖positions patch - collapsed patch‖) =
        2 * ‖firstSeparation / 2‖ + 2 * ‖secondSeparation / 2‖ := by
      simp [positions, collapsed, twoDipoleConfiguration, Fin.sum_univ_succ, norm_neg]
      ring
    rw [identity]
    linarith
  have actual := pointSourceTaylorCoefficient_relative_summable_and_tsum_le positions collapsed
    (observation - center) circulation receiverNonnegative (norm_nonneg _) positive weightNonnegative separated
    positionsBound collapsedBound small
  simp only [zeroCoefficient, sub_zero] at actual
  refine ⟨actual.1, actual.2.trans ?_⟩
  rw [moment]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sub_nonneg.mpr small.le))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_left
  have bounded := mul_le_mul_of_nonneg_left differenceSum
    (show 0 ≤ 32 * distance⁻¹ ^ 4 * radius by dsimp only [radius]; positivity)
  exact bounded.trans_eq (by dsimp only [radius]; ring)

end EulerNonuniqueness.Section6
