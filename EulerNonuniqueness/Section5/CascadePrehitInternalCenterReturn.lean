import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent
import EulerNonuniqueness.Section6.PaperRelativeCenterField

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 6000000

theorem Scales.eventually_cascade_prehit_internal_center_return (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant threshold referenceConstant factor : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 100) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      ‖fourPointArithmeticCenter (fourPointField
          (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid first time index patch)) -
        fourPointArithmeticCenter (fourPointField
          (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid second time index patch))‖ / changed.location (index.val + 1) ≤
      (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2 /
        (factor ^ 2 * changed.location (index.val + 1) ^ 2)) *
          ‖relativeNormalizedFirstMoment changed first second index time‖ +
      (96 * changed.omega (index.val + 1) / factor ^ 4) *
        (‖centroidAsymmetry second time index‖ / changed.location (index.val + 1)) *
        (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
          (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
            changed.length (index.val + 1)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative thresholdSmall referenceNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative] with frequency frequencyPositive extents mechanical
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal
    finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have safeTime : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 :=
    ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have geometry := (mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index).1
  have actualExtent := extents prepared path (factorSmall.trans (by norm_num)) index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  have different (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :
      positive ≠ negative := by
    intro equality
    have values := congrArg Fin.val equality
    omega
  have firstSeparated (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :=
    path.internal_centroid_gap safeTime index positive negative (different positive negative positiveBound negativeBound)
  have secondSeparated (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :
      factor * changed.length (index.val + 1) ≤
        ‖patchCentroid prepared.reference time index positive - patchCentroid prepared.reference time index negative‖ := by
    have actual := geometry.internalSeparated positive negative
      (Ne.symm (different positive negative positiveBound negativeBound))
    rw [prepared.referenceIdentity]
    apply (show factor * changed.length (index.val + 1) ≤ changed.length (index.val + 1) / 100 from by
      nlinarith [mul_le_mul_of_nonneg_right factorSmall (changed.length_pos (index.val + 1)).le]).trans
    exact actual
  have actual := quadrupole_internal_center_field_relative_bound changed
    prepared.trajectory.movingFamily.patchMotion prepared.reference index time frequencyPositive
    (show 0 < changed.ratio by change 0 < scales.ratio; linarith) factorPositive (by norm_num : (0 : ℝ) ≤ 3)
    (fun patch => (actualExtent patch).1)
    (fun patch => by rw [prepared.referenceIdentity]; exact (actualExtent patch).2)
    firstSeparated secondSeparated
  convert actual using 1 <;> ring

end EulerNonuniqueness.Paper
