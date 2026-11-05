import EulerNonuniqueness.Section5.CascadePrehitFirstMomentRate

noncomputable section

namespace EulerNonuniqueness.Paper

theorem quadrupoleNormalizedCentroidOffsets_relative_norm_scale
    {count : ℕ} (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    {radius length : ℝ} (radiusPositive : 0 < radius) (lengthPositive : 0 < length) :
    ‖quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius‖ =
      (length / radius) * ‖quadrupoleNormalizedCentroidOffsets first index time length -
        quadrupoleNormalizedCentroidOffsets second index time length‖ := by
  have identity : quadrupoleNormalizedCentroidOffsets first index time radius -
      quadrupoleNormalizedCentroidOffsets second index time radius =
      ((length / radius : ℝ) : ℂ) • (quadrupoleNormalizedCentroidOffsets first index time length -
        quadrupoleNormalizedCentroidOffsets second index time length) := by
    ext patch
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, quadrupoleNormalizedCentroidOffsets,
      Complex.ofReal_div]
    field_simp [show (length : ℂ) ≠ 0 by exact_mod_cast lengthPositive.ne',
      show (radius : ℂ) ≠ 0 by exact_mod_cast radiusPositive.ne']
    <;> ring
  rw [identity, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos lengthPositive radiusPositive)]

theorem quadrupoleNeutralSeriesEnvelope_strong_normalization
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    {radius : ℝ} (radiusPositive : 0 < radius) :
    (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
      quadrupoleNeutralSeriesEnvelope scales first second index time radius
        (3 * scales.length (index.val + 1) / radius) =
      ‖quadrupoleExteriorCoefficient scales first index time radius 0‖ *
        ‖relativeNormalizedFirstMoment scales first second index time‖ +
      ‖quadrupoleExteriorCoefficient scales first index time radius 0 - quadrupoleExteriorCoefficient scales second index time radius 0‖ *
        (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2 * ‖centroidAsymmetry second time index‖) +
      (24 * scales.location (index.val + 1) / radius) *
        (∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1)‖) *
        ‖quadrupoleNormalizedCentroidOffsets first index time (scales.length (index.val + 1)) -
          quadrupoleNormalizedCentroidOffsets second index time (scales.length (index.val + 1))‖ +
      (36 * scales.location (index.val + 1) / radius) *
        (∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1) -
          quadrupoleExteriorCoefficient scales second index time radius (power + 1)‖) +
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        ‖quadrupoleExternalReceiverAverage scales first index time - quadrupoleExternalReceiverAverage scales second index time‖ := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have weightPositive : 0 < 4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2 :=
    div_pos (mul_pos (by norm_num) (scales.location_pos _)) (sq_pos_of_pos lengthPositive)
  rw [quadrupoleNeutralSeriesEnvelope,
    quadrupoleNormalizedCentroidOffsets_relative_norm_scale first second index time radiusPositive lengthPositive,
    relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos weightPositive]
  field_simp [lengthPositive.ne', radiusPositive.ne']
  <;> ring

end EulerNonuniqueness.Paper
