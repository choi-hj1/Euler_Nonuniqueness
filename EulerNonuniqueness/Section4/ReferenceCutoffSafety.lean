import EulerNonuniqueness.Section4.ReferenceControlledCutoffFamily

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

local instance referenceCutoffSafetyHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance referenceCutoffSafetyC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem reference_cutoff_margin_of_geometric_bounds {count : ℕ} (countPositive : 0 < count)
    (scales : Scales) (configuration : FiniteContourConfiguration (count * 4))
    (radiusEquation : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1))
    {motion : PatchMotion count} {time shapeRadius gap margin : ℝ}
    (shapePositive : 0 < shapeRadius) (marginShape : margin ≤ shapeRadius / 8) (marginUnit : margin ≤ 1 / 8)
    (marginSlack : ∀ first second : Fin count × Fin 4,
      gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second)
    (state : MovingContourState (count * 4))
    (centerEquation : ∀ (index : Fin count) (patch : Fin 4), state.2.1 (finProdFinEquiv (index, patch)) =
      patchCentroid motion time index patch)
    (centersBounded : ∀ label, ‖state.2.1 label‖ ≤ 3)
    (shapesBounded : ∀ label, ‖state.2.2 label - standardCircleBanach‖ ≤ shapeRadius / 2)
    (differenceLower : ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : ∀ index : Fin count, diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter motion time receiver - quadrupoleCenter motion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) :
    2 * margin ≤ infDist state (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := by
  apply configuration.movingStateAdmissible_infDist_lower_bound (Nat.mul_pos countPositive (by norm_num)) (by norm_num)
  · intro label
    linarith [centersBounded label]
  · intro label
    linarith [shapesBounded label]
  · intro first second different
    have indexDifferent : finProdFinEquiv.symm first ≠ finProdFinEquiv.symm second :=
      fun equality => different (finProdFinEquiv.symm.injective equality)
    have separation := reference_centroid_pair_cutoff_slack scales motion time differenceLower differenceUpper
      radialSmall asymmetrySmall centerSeparation lengthSmall radiusSmall
      (finProdFinEquiv.symm first) (finProdFinEquiv.symm second) indexDifferent
    have slack := marginSlack (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
    have firstRadius := radiusEquation (finProdFinEquiv.symm first).1 (finProdFinEquiv.symm first).2
    have secondRadius := radiusEquation (finProdFinEquiv.symm second).1 (finProdFinEquiv.symm second).2
    have firstCenter := centerEquation (finProdFinEquiv.symm first).1 (finProdFinEquiv.symm first).2
    have secondCenter := centerEquation (finProdFinEquiv.symm second).1 (finProdFinEquiv.symm second).2
    simp only [Prod.mk.eta, Equiv.apply_symm_apply] at firstRadius secondRadius firstCenter secondCenter
    rw [firstRadius, secondRadius, firstCenter, secondCenter]
    linarith

end EulerNonuniqueness.Paper
