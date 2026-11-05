import EulerNonuniqueness.Section6.ComplexExteriorSeriesSmallBall
import EulerNonuniqueness.Section6.PaperRelativeNeutralPointSeries
import EulerNonuniqueness.Section6.PaperRelativeNeutralExternal

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem relative_quadrupoleCenteredExternalIncrement_series_bound
    {count : ℕ} {scales : Scales} {first second : PatchMotion count} {horizon time : ℝ}
    (firstEvolution : FinitePatchEvolution scales first horizon)
    (secondEvolution : FinitePatchEvolution scales second horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) {radius firstDistance secondDistance extent : ℝ}
    (radiusPositive : 0 < radius) (firstDistancePositive : 0 < firstDistance) (secondDistancePositive : 0 < secondDistance)
    (firstSmall : radius < firstDistance) (secondSmall : radius < secondDistance)
    (extentNonnegative : 0 ≤ extent) (extentSmall : extent ≤ 1 / 2)
    (firstSeparated : ∀ source ∈ Function.support (externalPatchVorticity scales first time index),
      firstDistance ≤ ‖quadrupoleCenter first time index - source‖)
    (secondSeparated : ∀ source ∈ Function.support (externalPatchVorticity scales second time index),
      secondDistance ≤ ‖quadrupoleCenter second time index - source‖)
    (firstBound : ∀ patch, ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ extent * radius)
    (secondBound : ∀ patch, ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ extent * radius) :
    ‖quadrupoleCenteredExternalIncrement scales second index time‖ ≤
      radius * extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales second index time radius power‖ ∧
    ‖quadrupoleCenteredExternalIncrement scales first index time - quadrupoleCenteredExternalIncrement scales second index time‖ ≤
      radius * (2 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius power‖) *
        ‖quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius‖ +
        extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius power -
          quadrupoleExteriorCoefficient scales second index time radius power‖) := by
  have firstSummable := exteriorVorticityCoefficient_norm_summable
    (firstEvolution.externalPatchVorticity_integrable inside index) (quadrupoleCenter first time index)
    radiusPositive.le firstDistancePositive firstSeparated firstSmall
  have secondSummable := exteriorVorticityCoefficient_norm_summable
    (secondEvolution.externalPatchVorticity_integrable inside index) (quadrupoleCenter second time index)
    radiusPositive.le secondDistancePositive secondSeparated secondSmall
  have differenceSummable : Summable (fun power : ℕ =>
      ‖quadrupoleExteriorCoefficient scales first index time radius power -
        quadrupoleExteriorCoefficient scales second index time radius power‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (firstSummable.add secondSummable)
  have normalizedIdentity (motion : PatchMotion count) (patch : Fin 4) : radius *
      ‖quadrupoleNormalizedCentroidOffsets motion index time radius patch‖ =
      ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ := by
    simp only [quadrupoleNormalizedCentroidOffsets, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos radiusPositive]
    field_simp
  have normalizedBound (motion : PatchMotion count)
      (bound : ∀ patch, ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ extent * radius)
      (patch : Fin 4) : ‖quadrupoleNormalizedCentroidOffsets motion index time radius patch‖ ≤ extent := by
    apply (mul_le_mul_left radiusPositive).mp
    rw [normalizedIdentity]
    exact (bound patch).trans_eq (by ring)
  have series (motion : PatchMotion count) (evolution : FinitePatchEvolution scales motion horizon)
      {distance : ℝ} (distancePositive : 0 < distance) (radiusSmall : radius < distance)
      (separated : ∀ source ∈ Function.support (externalPatchVorticity scales motion time index),
        distance ≤ ‖quadrupoleCenter motion time index - source‖)
      (bound : ∀ patch, ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ extent * radius)
      (patch : Fin 4) :
      HasSum (fun power : ℕ => quadrupoleExteriorCoefficient scales motion index time radius power *
        star (quadrupoleNormalizedCentroidOffsets motion index time radius patch) ^ (power + 1))
        ((radius : ℂ)⁻¹ * quadrupoleCenteredExternalIncrement scales motion index time patch) := by
    have pointInside : radius * ‖quadrupoleNormalizedCentroidOffsets motion index time radius patch‖ / distance < 1 := by
      apply (div_lt_one distancePositive).mpr
      rw [normalizedIdentity]
      exact (bound patch).trans_lt (by nlinarith)
    have actual := exterior_biotSavart_series_hasSum (evolution.externalPatchVorticity_integrable inside index)
      (evolution.externalPatchVorticity_memLp inside index (ENNReal.ofReal (4 : ℝ)))
      (quadrupoleCenter motion time index) (quadrupoleNormalizedCentroidOffsets motion index time radius patch)
      radiusPositive distancePositive separated pointInside
    have evaluation : quadrupoleCenter motion time index + (radius : ℂ) *
        quadrupoleNormalizedCentroidOffsets motion index time radius patch = patchCentroid motion time index patch := by
      dsimp only [quadrupoleNormalizedCentroidOffsets]
      field_simp [Complex.ofReal_ne_zero.mpr radiusPositive.ne']
      <;> ring
    simpa only [quadrupoleExteriorCoefficient, quadrupoleCenteredExternalIncrement, evaluation] using actual
  have firstSeries := series first firstEvolution firstDistancePositive firstSmall firstSeparated firstBound
  have secondSeries := series second secondEvolution secondDistancePositive secondSmall secondSeparated secondBound
  have firstSumNonnegative : 0 ≤ ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius power‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro patch
    have actual := complexExteriorSeries_norm_le _ _ extentNonnegative (by linarith : extent ≤ 1)
      (normalizedBound second secondBound patch) (secondSeries patch) secondSummable
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive] at actual
    have divided : ‖quadrupoleCenteredExternalIncrement scales second index time patch‖ / radius ≤
        extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales second index time radius power‖ := by
      simpa only [div_eq_mul_inv, mul_comm] using actual
    exact ((div_le_iff₀ radiusPositive).mp divided).trans_eq (by ring)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro patch
    have actual := complexExteriorSeries_relative_small_ball_le _ _ _ _ extentNonnegative extentSmall
      (normalizedBound first firstBound patch) (normalizedBound second secondBound patch)
      (firstSeries patch) (secondSeries patch) firstSummable differenceSummable
    rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive] at actual
    have pointDifference := norm_le_pi_norm
      (quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius) patch
    simp only [Pi.sub_apply] at pointDifference
    have enlarged := actual.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left pointDifference (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) firstSumNonnegative)) _)
    have divided : ‖quadrupoleCenteredExternalIncrement scales first index time patch -
        quadrupoleCenteredExternalIncrement scales second index time patch‖ / radius ≤
        2 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius power‖) *
          ‖quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius‖ +
        extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius power -
          quadrupoleExteriorCoefficient scales second index time radius power‖ := by
      simpa only [div_eq_mul_inv, mul_comm] using enlarged
    exact ((div_le_iff₀ radiusPositive).mp divided).trans_eq (by ring)

end EulerNonuniqueness.Paper
