import EulerNonuniqueness.Section3.ExteriorCentroidResponse
import EulerNonuniqueness.General.WeightedTailDilation

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem contourExteriorCentroidResponse_exists_dilated_relative_ball :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart initial) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ phase : Circle, ∀ firstCoefficients secondCoefficients : ℕ → ℂ,
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power‖) →
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖secondCoefficients power‖) →
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power - secondCoefficients power‖) →
      ∀ ratio : ℝ, 0 ≤ ratio → ratio ≤ 1 →
      ‖contourExteriorCentroidResponse phase (fun power => ratio ^ power • firstCoefficients power)
          (diskPhysicalSpectralChart initial) -
        contourExteriorCentroidResponse phase (fun power => ratio ^ power • secondCoefficients power)
          (diskPhysicalSpectralChart final)‖ ≤
      constant * ratio * ((∑' power, (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power‖) *
          (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskNeutralCLM initial - diskNeutralCLM final‖) +
        (∑' power, (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power - secondCoefficients power‖) *
          ‖diskPhysicalTransverseProjection final‖) := by
  obtain ⟨radius, radiusPositive, constant, nonnegative, bound⟩ :=
    contourExteriorCentroidResponse_exists_spectral_relative_ball
  refine ⟨radius, radiusPositive, constant, nonnegative, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea initialCentered finalCentered phase
    firstCoefficients secondCoefficients firstSummable secondSummable differenceSummable ratio
    ratioNonnegative ratioSmall
  let firstDilated := fun power : ℕ => ratio ^ power • firstCoefficients power
  let secondDilated := fun power : ℕ => ratio ^ power • secondCoefficients power
  let firstTail := exteriorCoefficientWithoutLeading firstDilated
  let secondTail := exteriorCoefficientWithoutLeading secondDilated
  let budget := ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
    (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
      ‖diskNeutralCLM initial - diskNeutralCLM final‖
  have firstTailBound := EulerNonuniqueness.General.summable_weighted_tail_dilation firstCoefficients
    (by norm_num : (0 : ℝ) ≤ 96) ratioNonnegative ratioSmall firstSummable
  have secondTailBound := EulerNonuniqueness.General.summable_weighted_tail_dilation secondCoefficients
    (by norm_num : (0 : ℝ) ≤ 96) ratioNonnegative ratioSmall secondSummable
  have differenceTailBound := EulerNonuniqueness.General.summable_weighted_tail_dilation
    (fun power => firstCoefficients power - secondCoefficients power)
    (by norm_num : (0 : ℝ) ≤ 96) ratioNonnegative ratioSmall differenceSummable
  have firstIdentity (power : ℕ) : firstTail power =
      if power = 0 then 0 else ratio ^ power • firstCoefficients power := rfl
  have secondIdentity (power : ℕ) : secondTail power =
      if power = 0 then 0 else ratio ^ power • secondCoefficients power := rfl
  have differenceIdentity (power : ℕ) : firstTail power - secondTail power =
      if power = 0 then 0 else ratio ^ power • (firstCoefficients power - secondCoefficients power) := by
    by_cases zero : power = 0 <;> simp only [firstIdentity, secondIdentity, zero, if_true,
      if_false, sub_self, smul_sub]
  have actual := bound initial final initialInside finalInside initialArea finalArea phase firstTail secondTail
    (by simpa only [firstIdentity] using firstTailBound.1)
    (by simpa only [secondIdentity] using secondTailBound.1)
    (by simpa only [differenceIdentity] using differenceTailBound.1)
  have firstAreaNonzero : contourAreaFunctional (diskPhysicalSpectralChart initial) ≠ 0 := by
    change diskSpectralTubularArea initial ≠ 0
    rw [initialArea]
    exact Real.pi_ne_zero
  have finalAreaNonzero : contourAreaFunctional (diskPhysicalSpectralChart final) ≠ 0 := by
    change diskSpectralTubularArea final ≠ 0
    rw [finalArea]
    exact Real.pi_ne_zero
  rw [contourExteriorCentroidResponse_without_leading phase _ _ initialCentered firstAreaNonzero,
    contourExteriorCentroidResponse_without_leading phase _ _ finalCentered finalAreaNonzero]
  change ‖contourExteriorCentroidResponse phase firstTail (diskPhysicalSpectralChart initial) -
    contourExteriorCentroidResponse phase secondTail (diskPhysicalSpectralChart final)‖ ≤ _
  apply actual.trans
  have firstEstimate := mul_le_mul_of_nonneg_right firstTailBound.2
    (show 0 ≤ budget by dsimp only [budget]; positivity)
  have differenceEstimate := mul_le_mul_of_nonneg_right differenceTailBound.2
    (norm_nonneg (diskPhysicalTransverseProjection final))
  have estimate := mul_le_mul_of_nonneg_left (add_le_add firstEstimate differenceEstimate) nonnegative
  simpa only [← firstIdentity, ← differenceIdentity, budget, mul_add, mul_assoc, mul_left_comm] using estimate

end EulerNonuniqueness.Paper
