import EulerNonuniqueness.Section5.CascadeQuadrupoleMacroSupport
import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent
import EulerNonuniqueness.Section5.CascadeRelativeFirstMomentHistory
import EulerNonuniqueness.Section6.PaperRelativeFirstMomentRate

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

def quadrupoleNeutralSeriesEnvelope {count : ℕ} (scales : Scales) (first second : PatchMotion count)
    (index : Fin count) (time radius extent : ℝ) : ℝ :=
  radius * (‖quadrupoleExteriorCoefficient scales first index time radius 0‖ *
    (‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ / radius) +
    ‖quadrupoleExteriorCoefficient scales first index time radius 0 - quadrupoleExteriorCoefficient scales second index time radius 0‖ *
    (‖centroidAsymmetry second time index‖ / radius) +
    (2 * extent * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1)‖) *
    ‖quadrupoleNormalizedCentroidOffsets first index time radius - quadrupoleNormalizedCentroidOffsets second index time radius‖ +
    extent ^ 2 * ∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1) -
      quadrupoleExteriorCoefficient scales second index time radius (power + 1)‖) +
    ‖quadrupoleExternalReceiverAverage scales first index time - quadrupoleExternalReceiverAverage scales second index time‖

def relativeFirstMomentExternalVelocity {count : ℕ} (scales : Scales) (first second : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℂ :=
  (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) •
    (quadrupoleNeutralExternalVelocity scales first index time - quadrupoleNeutralExternalVelocity scales second index time)

theorem Scales.eventually_cascade_prehit_firstMoment_rate (scales : Scales)
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
      let extent := 3 * changed.length (index.val + 1) / radius
      HasDerivAt (relativeNormalizedFirstMoment changed first second index)
        (relativeFirstMomentExternalVelocity changed first second index time) time ∧
      ‖relativeFirstMomentExternalVelocity changed first second index time‖ ≤
        (4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2) *
          quadrupoleNeutralSeriesEnvelope changed first second index time radius extent := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_quadrupole_macro_support amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive
      (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) thresholdSmall referenceNonnegative,
    scales.eventually_length_lt_location ratioBound alphaPositive
      (show 0 < factor / 235929600 by positivity)] with frequency frequencyLarge support extentBound lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound
    radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let extent := 3 * changed.length (index.val + 1) / radius
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have distancePositive : 0 < changed.location (index.val + 1) / 1000 := by positivity
  have radiusSmall : radius < changed.location (index.val + 1) / 1000 := by
    dsimp only [radius]
    nlinarith [changed.location_pos (index.val + 1), mul_le_mul_of_nonneg_right factorSmall
      (changed.location_pos (index.val + 1)).le]
  have extentNonnegative : 0 ≤ extent := by dsimp only [extent]; positivity
  have extentSmall : extent ≤ 1 / 2 := by
    apply (div_le_iff₀ radiusPositive).mpr
    have actual := (lengths (index.val + 1)).le
    change changed.length (index.val + 1) ≤ factor / 235929600 * changed.location (index.val + 1) at actual
    dsimp only [radius]
    linarith
  have extentIdentity : extent * radius = 3 * changed.length (index.val + 1) := by
    dsimp only [extent]
    exact div_mul_cancel₀ _ radiusPositive.ne'
  have firstBound (patch : Fin 4) : ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ extent * radius := by
    rw [extentIdentity]
    exact (extentBound prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside patch).1
  have secondBound (patch : Fin 4) : ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ extent * radius := by
    rw [extentIdentity]
    simpa only [second, prepared.referenceIdentity] using
      (extentBound prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside patch).2
  have sourceSupport := support count phase dipoleAngle prepared path time fullInside index
  have firstSupport : ∀ source ∈ Function.support (externalPatchVorticity changed first time index),
      changed.location (index.val + 1) / 1000 ≤ ‖quadrupoleCenter first time index - source‖ := sourceSupport.2
  have secondSupport : ∀ source ∈ Function.support (externalPatchVorticity changed second time index),
      changed.location (index.val + 1) / 1000 ≤ ‖quadrupoleCenter second time index - source‖ := by
    simpa only [second, prepared.referenceIdentity] using sourceSupport.1
  have referenceEvolution : FinitePatchEvolution changed second path.stop := by
    simpa only [second, prepared.referenceIdentity] using
      prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound])
  have bound := relative_firstMoment_external_rate_bound path.evolution referenceEvolution fullInside
    amplitudePositive frequencyPositive ratioPositive index radiusPositive distancePositive distancePositive radiusSmall radiusSmall
    extentNonnegative extentSmall firstSupport secondSupport firstBound secondBound
  constructor
  · exact path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index fullInside
  · have weightPositive : 0 < 4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2 := by
      exact div_pos (mul_pos (by norm_num) (changed.location_pos _)) (sq_pos_of_pos (changed.length_pos _))
    change ‖relativeFirstMomentExternalVelocity changed first second index time‖ ≤
      (4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2) *
        quadrupoleNeutralSeriesEnvelope changed first second index time radius extent
    rw [relativeFirstMomentExternalVelocity, norm_smul, Real.norm_eq_abs, abs_of_pos weightPositive]
    exact bound

end EulerNonuniqueness.Paper
