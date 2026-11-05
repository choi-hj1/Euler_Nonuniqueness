import EulerNonuniqueness.Section6.PaperNeutralPointReceiverSplit

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem relative_firstMoment_external_rate_bound
    {count : ℕ} {scales : Scales} {first second : PatchMotion count} {horizon time : ℝ}
    (firstEvolution : FinitePatchEvolution scales first horizon)
    (secondEvolution : FinitePatchEvolution scales second horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) {radius firstDistance secondDistance extent : ℝ}
    (radiusPositive : 0 < radius) (firstDistancePositive : 0 < firstDistance) (secondDistancePositive : 0 < secondDistance)
    (firstSmall : radius < firstDistance) (secondSmall : radius < secondDistance)
    (extentNonnegative : 0 ≤ extent) (extentSmall : extent ≤ 1 / 2)
    (firstSeparated : ∀ source ∈ Function.support (externalPatchVorticity scales first time index),
      firstDistance ≤ ‖quadrupoleCenter first time index - source‖)
    (secondSeparated : ∀ source ∈ Function.support (externalPatchVorticity scales second time index),
      secondDistance ≤ ‖quadrupoleCenter second time index - source‖)
    (firstBound : ∀ patch, ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ extent * radius)
    (secondBound : ∀ patch, ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ extent * radius) :
    (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        ‖quadrupoleNeutralExternalVelocity scales first index time - quadrupoleNeutralExternalVelocity scales second index time‖ ≤
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        (radius * (‖quadrupoleExteriorCoefficient scales first index time radius 0‖ *
          (‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ / radius) +
          ‖quadrupoleExteriorCoefficient scales first index time radius 0 - quadrupoleExteriorCoefficient scales second index time radius 0‖ *
          (‖centroidAsymmetry second time index‖ / radius) +
          (2 * extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1)‖) *
          ‖quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius‖ +
          extent ^ 2 * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1) -
            quadrupoleExteriorCoefficient scales second index time radius (power + 1)‖) +
          ‖quadrupoleExternalReceiverAverage scales first index time - quadrupoleExternalReceiverAverage scales second index time‖) := by
  have pointBound := relative_quadrupoleExternalPointAverage_signed_series_bound firstEvolution secondEvolution inside index
    radiusPositive firstDistancePositive secondDistancePositive firstSmall secondSmall extentNonnegative extentSmall
    firstSeparated secondSeparated firstBound secondBound
  have pointBound' := (div_le_iff₀ radiusPositive).mp pointBound
  have split := relative_quadrupoleNeutralExternalVelocity_norm_le_point_receiver firstEvolution secondEvolution inside
    amplitudePositive frequencyPositive ratioPositive index
  have total := split.trans (add_le_add_right pointBound' _)
  have weightNonnegative : 0 ≤ 4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (scales.location_pos (index.val + 1)).le) (sq_nonneg _)
  convert mul_le_mul_of_nonneg_left total weightNonnegative using 1 <;> ring

end EulerNonuniqueness.Paper
