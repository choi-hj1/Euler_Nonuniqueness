import EulerNonuniqueness.Section6.PaperNeutralExteriorSeries
import EulerNonuniqueness.Section6.SignedExteriorSeriesSmallBall

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem exteriorVorticityCoefficient_norm_summable {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distancePositive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖)
    (small : radius < distance) :
    Summable (fun power : ℕ => ‖exteriorVorticityCoefficient vorticity center radius power‖) := by
  have geometric := (summable_geometric_of_lt_one (div_nonneg radiusNonnegative distancePositive.le)
    ((div_lt_one distancePositive).mpr small)).mul_right
      ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_exteriorVorticityCoefficient_le integrable center radiusNonnegative distancePositive separated) geometric

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleExteriorCoefficient {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time radius : ℝ) (power : ℕ) : ℂ :=
  exteriorVorticityCoefficient (externalPatchVorticity scales motion time index)
    (quadrupoleCenter motion time index) radius power

theorem relative_quadrupoleExternalPointAverage_signed_series_bound
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
    ‖quadrupoleExternalPointAverage scales first index time - quadrupoleExternalPointAverage scales second index time‖ / radius ≤
      ‖quadrupoleExteriorCoefficient scales first index time radius 0‖ *
        (‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ / radius) +
      ‖quadrupoleExteriorCoefficient scales first index time radius 0 - quadrupoleExteriorCoefficient scales second index time radius 0‖ *
        (‖centroidAsymmetry second time index‖ / radius) +
      (2 * extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1)‖) *
        ‖quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius‖ +
      extent ^ 2 * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1) -
        quadrupoleExteriorCoefficient scales second index time radius (power + 1)‖ := by
  have firstNormSummable := exteriorVorticityCoefficient_norm_summable
    (firstEvolution.externalPatchVorticity_integrable inside index) (quadrupoleCenter first time index)
    radiusPositive.le firstDistancePositive firstSeparated firstSmall
  have secondNormSummable := exteriorVorticityCoefficient_norm_summable
    (secondEvolution.externalPatchVorticity_integrable inside index) (quadrupoleCenter second time index)
    radiusPositive.le secondDistancePositive secondSeparated secondSmall
  have firstTail := (summable_nat_add_iff 1).mpr firstNormSummable
  have secondTail := (summable_nat_add_iff 1).mpr secondNormSummable
  have differenceTail : Summable (fun power : ℕ =>
      ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1) -
        quadrupoleExteriorCoefficient scales second index time radius (power + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (firstTail.add secondTail)
  have normalizedBound (motion : PatchMotion count)
      (bound : ∀ patch, ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ extent * radius)
      (patch : Fin 4) : ‖quadrupoleNormalizedCentroidOffsets motion index time radius patch‖ ≤ extent := by
    simp only [quadrupoleNormalizedCentroidOffsets, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive]
    have actual := mul_le_mul_of_nonneg_left (bound patch) (inv_nonneg.mpr radiusPositive.le)
    exact actual.trans_eq (by field_simp)
  have firstSeries := firstEvolution.quadrupoleExternalPointAverage_signed_series inside index radiusPositive
    firstDistancePositive firstSeparated (fun patch => (firstBound patch).trans_lt (by nlinarith))
  have secondSeries := secondEvolution.quadrupoleExternalPointAverage_signed_series inside index radiusPositive
    secondDistancePositive secondSeparated (fun patch => (secondBound patch).trans_lt (by nlinarith))
  have actual := signedExteriorSeries_relative_small_ball_le
    (quadrupoleNormalizedCentroidOffsets first index time radius) (quadrupoleNormalizedCentroidOffsets second index time radius)
    (quadrupoleExteriorCoefficient scales first index time radius) (quadrupoleExteriorCoefficient scales second index time radius)
    extentNonnegative extentSmall (normalizedBound first firstBound) (normalizedBound second secondBound)
    firstSeries secondSeries firstTail differenceTail
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive,
    quadrupoleNormalizedCentroidOffsets_signed_average, quadrupoleNormalizedCentroidOffsets_signed_average,
    ← mul_sub, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive] at actual
  simpa only [div_eq_mul_inv, mul_comm] using actual

end EulerNonuniqueness.Paper
