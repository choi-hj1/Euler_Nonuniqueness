import EulerNonuniqueness.Section5.CascadePrehitCenteredExteriorReturn
import EulerNonuniqueness.Section6.PaperExternalDilationReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem quadrupoleNormalizedCentroidOffsets_relative_norm_eq_div
    {count : ℕ} (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    {length : ℝ} (lengthPositive : 0 < length) :
    ‖quadrupoleNormalizedCentroidOffsets first index time length - quadrupoleNormalizedCentroidOffsets second index time length‖ =
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length := by
  have identity : quadrupoleNormalizedCentroidOffsets first index time length -
      quadrupoleNormalizedCentroidOffsets second index time length =
      (length : ℂ)⁻¹ • ((fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)) := by
    ext patch
    simp only [quadrupoleNormalizedCentroidOffsets, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [identity, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive]
  ring

theorem Scales.eventually_cascade_prehit_external_dilation_return (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
        quadrupoleExteriorCoefficient changed second index time radius power‖
      |quadrupoleExternalDilationRate changed first index time - quadrupoleExternalDilationRate changed second index time| /
          changed.length (index.val + 1) ^ 2 ≤
        72 * (96 / Real.pi * (2304 * changed.strain)) *
          (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
            (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
              changed.length (index.val + 1)) + 36 * difference := by
  filter_upwards [scales.eventually_cascade_prehit_centered_exterior_return amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive
      (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) thresholdSmall referenceNonnegative]
    with frequency fields extents
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  have lengthPositive := changed.length_pos (index.val + 1)
  have actualFields := fields count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only at actualFields
  rw [quadrupoleNormalizedCentroidOffsets_relative_norm_eq_div first second index time lengthPositive] at actualFields
  have actual := quadrupole_external_dilation_rate_relative_bound changed first second index time
    (by norm_num : (0 : ℝ) ≤ 3) (fun patch =>
      (extents prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside patch).1)
  rw [show (4 : ℝ) * 3 = 12 by norm_num] at actual
  have firstTerm := mul_le_mul_of_nonneg_left actualFields.1 (show 0 ≤ 4 *
    (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
        changed.length (index.val + 1)) by positivity)
  have secondTerm := mul_le_mul_of_nonneg_left actualFields.2 (by norm_num : (0 : ℝ) ≤ 12)
  exact (actual.trans (add_le_add firstTerm secondTerm)).trans_eq (by ring)

end EulerNonuniqueness.Paper
