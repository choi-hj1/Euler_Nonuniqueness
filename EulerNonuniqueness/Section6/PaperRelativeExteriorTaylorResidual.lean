import EulerNonuniqueness.Section6.RelativeExteriorTaylorTail
import EulerNonuniqueness.Section6.PaperRelativeNeutralPointSeries
import EulerNonuniqueness.Section6.PaperExternalShapeForcing
import EulerNonuniqueness.Section4.ReferenceForeignStrainIdentity

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleExternalTaylorResidual {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : FourPointConfiguration :=
  fourPointExternalTaylorRemainder (biotSavart (externalPatchVorticity scales motion time index))
    (quadrupoleCenter motion time index)
    (vorticityComplexStrain (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index) •
      (Complex.conjCLE : ℂ →L[ℝ] ℂ)) (fun patch => patchCentroid motion time index patch)

set_option maxHeartbeats 3000000

theorem relative_quadrupoleExternalTaylorResidual_bound
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
    ‖quadrupoleExternalTaylorResidual scales first time index - quadrupoleExternalTaylorResidual scales second time index‖ / radius ≤
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
  have normalizedIdentity (motion : PatchMotion count) (patch : Fin 4) :
      quadrupoleCenter motion time index + (radius : ℂ) * quadrupoleNormalizedCentroidOffsets motion index time radius patch =
        patchCentroid motion time index patch := by
    dsimp only [quadrupoleNormalizedCentroidOffsets]
    field_simp [Complex.ofReal_ne_zero.mpr radiusPositive.ne']
    <;> ring
  have normalizedRadius (motion : PatchMotion count) (patch : Fin 4) : radius *
      ‖quadrupoleNormalizedCentroidOffsets motion index time radius patch‖ =
        ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ := by
    simp only [quadrupoleNormalizedCentroidOffsets, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive]
    field_simp
  have remainderIdentity (motion : PatchMotion count) (patch : Fin 4) :
      ((radius : ℂ)⁻¹ * (biotSavart (externalPatchVorticity scales motion time index)
          (patchCentroid motion time index patch) - biotSavart (externalPatchVorticity scales motion time index)
            (quadrupoleCenter motion time index))) -
        quadrupoleExteriorCoefficient scales motion index time radius 0 *
          star (quadrupoleNormalizedCentroidOffsets motion index time radius patch) =
      (radius : ℂ)⁻¹ * quadrupoleExternalTaylorResidual scales motion time index patch := by
    rw [quadrupoleExteriorCoefficient, exteriorVorticityCoefficient_zero_eq_complexStrain]
    dsimp only [quadrupoleExternalTaylorResidual, fourPointExternalTaylorRemainder, quadrupoleNormalizedCentroidOffsets]
    simp only [ContinuousLinearMap.smul_apply, Complex.conjCLE_apply, smul_eq_mul, star_mul, star_inv₀,
      Complex.star_def, Complex.conj_ofReal]
    ring <;> rfl
  let bound := (2 * extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1)‖) *
      ‖quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius‖ +
    extent ^ 2 * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1) -
      quadrupoleExteriorCoefficient scales second index time radius (power + 1)‖
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have pointwise (patch : Fin 4) : ‖(radius : ℂ)⁻¹ *
      (quadrupoleExternalTaylorResidual scales first time index patch - quadrupoleExternalTaylorResidual scales second time index patch)‖ ≤ bound := by
    have firstSeries := exterior_biotSavart_series_hasSum (firstEvolution.externalPatchVorticity_integrable inside index)
      (firstEvolution.externalPatchVorticity_memLp inside index (ENNReal.ofReal (4 : ℝ)))
      (quadrupoleCenter first time index) (quadrupoleNormalizedCentroidOffsets first index time radius patch)
      radiusPositive firstDistancePositive firstSeparated
      ((div_lt_one firstDistancePositive).mpr (by rw [normalizedRadius]; exact (firstBound patch).trans_lt (by nlinarith)))
    have secondSeries := exterior_biotSavart_series_hasSum (secondEvolution.externalPatchVorticity_integrable inside index)
      (secondEvolution.externalPatchVorticity_memLp inside index (ENNReal.ofReal (4 : ℝ)))
      (quadrupoleCenter second time index) (quadrupoleNormalizedCentroidOffsets second index time radius patch)
      radiusPositive secondDistancePositive secondSeparated
      ((div_lt_one secondDistancePositive).mpr (by rw [normalizedRadius]; exact (secondBound patch).trans_lt (by nlinarith)))
    rw [normalizedIdentity] at firstSeries secondSeries
    have actual := antilinear_series_relative_tail_bound _ _
      (quadrupoleExteriorCoefficient scales first index time radius) (quadrupoleExteriorCoefficient scales second index time radius)
      extentNonnegative extentSmall (normalizedBound first firstBound patch) (normalizedBound second secondBound patch)
      firstSeries secondSeries firstTail differenceTail
    rw [remainderIdentity, remainderIdentity, ← mul_sub] at actual
    exact actual.trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (norm_le_pi_norm (quadrupoleNormalizedCentroidOffsets first index time radius -
        quadrupoleNormalizedCentroidOffsets second index time radius) patch) (by positivity)) _)
  have uniform := (pi_norm_le_iff_of_nonneg boundNonnegative).mpr pointwise
  change ‖fun patch => (radius : ℂ)⁻¹ *
    (quadrupoleExternalTaylorResidual scales first time index patch - quadrupoleExternalTaylorResidual scales second time index patch)‖ ≤ bound at uniform
  change ‖(radius : ℂ)⁻¹ •
    (quadrupoleExternalTaylorResidual scales first time index - quadrupoleExternalTaylorResidual scales second time index)‖ ≤ bound at uniform
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive] at uniform
  simpa only [bound, div_eq_mul_inv, mul_comm] using uniform

end EulerNonuniqueness.Paper
