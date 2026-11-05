import EulerNonuniqueness.Section5.CascadePrehitCenteredExteriorReturn
import EulerNonuniqueness.Section6.PaperRelativeExteriorTaylorResidual

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_prehit_exterior_taylor_return (scales : Scales)
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
      let length := changed.length (index.val + 1)
      let radius := factor / 39321600 * changed.location (index.val + 1)
      ‖quadrupoleExternalTaylorResidual changed first time index - quadrupoleExternalTaylorResidual changed second time index‖ /
          length ≤ (length / radius) *
        (6 * (96 / Real.pi * (2304 * changed.strain)) *
          ‖quadrupoleNormalizedCentroidOffsets first index time length -
            quadrupoleNormalizedCentroidOffsets second index time length‖ +
          9 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1) -
            quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖)) := by
  filter_upwards [scales.eventually_cascade_quadrupole_foreign_head_tail amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_quadrupole_macro_support amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive
      (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) thresholdSmall referenceNonnegative,
    scales.eventually_length_lt_location ratioBound alphaPositive
      (show 0 < factor / 235929600 by positivity)] with frequency coefficients support extents lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let extent := 3 * length / radius
  let budget := 96 / Real.pi * (2304 * changed.strain)
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have distancePositive : 0 < changed.location (index.val + 1) / 1000 := by positivity
  have radiusSmall : radius < changed.location (index.val + 1) / 1000 := by
    dsimp only [radius]
    nlinarith [mul_le_mul_of_nonneg_right factorSmall locationPositive.le]
  have extentNonnegative : 0 ≤ extent := by dsimp only [extent]; positivity
  have extentSmall : extent ≤ 1 / 2 := by
    apply (div_le_iff₀ radiusPositive).mpr
    have actual := (lengths (index.val + 1)).le
    change length ≤ factor / 235929600 * changed.location (index.val + 1) at actual
    dsimp only [radius]
    linarith
  have extentIdentity : extent * radius = 3 * length := by
    dsimp only [extent]
    exact div_mul_cancel₀ _ radiusPositive.ne'
  have actualExtent := extents prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have firstBound (patch : Fin 4) : ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ extent * radius := by
    rw [extentIdentity]
    exact (actualExtent patch).1
  have secondBound (patch : Fin 4) : ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ extent * radius := by
    rw [extentIdentity]
    simpa only [second, prepared.referenceIdentity] using (actualExtent patch).2
  have actualSupport := support count phase dipoleAngle prepared path time fullInside index
  have secondSupport : ∀ source ∈ Function.support (externalPatchVorticity changed second time index),
      changed.location (index.val + 1) / 1000 ≤ ‖quadrupoleCenter second time index - source‖ := by
    simpa only [second, prepared.referenceIdentity] using actualSupport.1
  have referenceEvolution : FinitePatchEvolution changed second path.stop := by
    simpa only [second, prepared.referenceIdentity] using
      prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound])
  have actual := relative_quadrupoleExternalTaylorResidual_bound path.evolution referenceEvolution fullInside index
    radiusPositive distancePositive distancePositive radiusSmall radiusSmall extentNonnegative extentSmall
    actualSupport.2 secondSupport firstBound secondBound
  rw [quadrupoleNormalizedCentroidOffsets_relative_norm_scale first second index time radiusPositive lengthPositive] at actual
  have firstCoefficients := coefficients count phase dipoleAngle prepared path time fullInside index 0
  change Summable (fun power => ‖quadrupoleExteriorCoefficient changed first index time radius power‖) ∧
    ‖quadrupoleExteriorCoefficient changed first index time radius 0‖ ≤ budget ∧
    (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1)‖) ≤ budget at firstCoefficients
  have enlarged := actual.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left firstCoefficients.2.2
      (show 0 ≤ 2 * extent by positivity))
      (show 0 ≤ (length / radius) * ‖quadrupoleNormalizedCentroidOffsets first index time length -
        quadrupoleNormalizedCentroidOffsets second index time length‖ by positivity)) _)
  have scaled := mul_le_mul_of_nonneg_left enlarged (div_nonneg radiusPositive.le lengthPositive.le)
  have cancel : (radius / length) *
      (‖quadrupoleExternalTaylorResidual changed first time index - quadrupoleExternalTaylorResidual changed second time index‖ / radius) =
      ‖quadrupoleExternalTaylorResidual changed first time index - quadrupoleExternalTaylorResidual changed second time index‖ / length := by
    field_simp
    <;> ring
  rw [cancel] at scaled
  apply scaled.trans_eq
  change (radius / length) *
    (2 * extent * budget * ((length / radius) * ‖quadrupoleNormalizedCentroidOffsets first index time length -
      quadrupoleNormalizedCentroidOffsets second index time length‖) + extent ^ 2 *
      (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1) -
        quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖)) =
    (length / radius) * (6 * budget *
      ‖quadrupoleNormalizedCentroidOffsets first index time length -
        quadrupoleNormalizedCentroidOffsets second index time length‖ +
      9 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1) -
        quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖))
  dsimp only [extent]
  field_simp [lengthPositive.ne', radiusPositive.ne']
  <;> ring

end EulerNonuniqueness.Paper
