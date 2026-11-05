import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent
import EulerNonuniqueness.Section6.PaperDilationForcingParts

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_prehit_patch_dilation_return (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {scaleRoot boundaryConstant threshold referenceConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius factor monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, factor ≤ 1 / 8 →
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      |quadrupolePatchDilationRate changed first index time - quadrupolePatchDilationRate changed second index time| /
          changed.length (index.val + 1) ^ 2 ≤
        4 * (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
          (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
            changed.length (index.val + 1)) *
          (‖quadrupoleDilationPatchError changed second index time‖ / changed.length (index.val + 1)) +
        12 * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ /
          changed.length (index.val + 1)) := by
  filter_upwards [scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive rootPositive
    boundaryNonnegative thresholdSmall referenceNonnegative] with frequency extents
  intro orbit sectionTime phase dipoleAngle shapeRadius factor monitor count prepared path factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside
  have actual := quadrupole_patch_dilation_rate_relative_bound {scales with frequency := frequency}
    prepared.trajectory.movingFamily.patchMotion prepared.reference index time (by norm_num : (0 : ℝ) ≤ 3)
    (fun patch => (extents prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside patch).1)
  convert actual using 1 <;> ring

end EulerNonuniqueness.Paper
