import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section4.ReferenceUniformShapeForcing
import EulerNonuniqueness.Section4.ReferenceNeutralNormalization

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem exists_uniform_coarse_reference_shape_forcing_bound :
    ∃ internalBound ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time memory bound : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      0 ≤ memory → 0 ≤ bound → scales.hessian ≤ 1 →
      (∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index) →
      (∀ index : Fin count, diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ index, |radialShape motion time index| ≤ 1 / 2) →
      (∀ index, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64) →
      (∀ receiver source : Fin count, receiver ≠ source →
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter motion time receiver - quadrupoleCenter motion time source‖) →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
      ∀ (deformation : Fin count → ℝ),
      (∀ index patch, BoundaryCloseToCircle scales motion time index patch (deformation index)) →
      (∀ index, 0 ≤ deformation index) → (∀ index, deformation index ≤ 1 / 16) →
      ∀ (index : Fin count),
      deformation index ≤ bound / scales.omega (index.val + 1) ^ 2 →
      scales.length (index.val + 1) ≤ 1 →
      ‖centroidAsymmetry motion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
      scales.length (index.val + 1) < radius / (8 * (memory + 1)) →
      let positions := fun patch => patchCentroid motion time index patch
      let point := fourPointOddPart positions
      let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
      |(pointShapeChart point.1 point.2).1| + |(pointShapeChart point.1 point.2).2| ≤ 1 / 4 →
      ‖pointShapeForcing point.1 point.2
          (fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)).1
          (fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)).2‖ ≤
        ((2 * internalBound * memory ^ 2 + 27648) / Real.pi) * scales.strain +
          ((414720000000 + 3397386240 / Real.pi) * bound / scales.amplitude) /
            scales.omega (index.val + 1) ^ 4 := by
  obtain ⟨internalBound, internalNonnegative, radius, radiusPositive, estimate⟩ :=
    exists_uniform_reference_shape_forcing_bound
  refine ⟨internalBound, internalNonnegative, radius, radiusPositive, ?_⟩
  intro count scales motion horizon time memory bound evolution inside amplitudePositive frequencyBound ratioBound
    alphaPositive memoryNonnegative boundNonnegative hessianBound differenceLower differenceUpper radialSmall
    asymmetrySmall centerSeparation lengthSmall radiusSmall deformation control nonnegative small index
    deformationBound lengthBound asymmetryBound normalizedSmall
  dsimp only
  intro chartSmall
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have geometry := evolution.reference_centroid_field_geometry inside amplitudePositive frequencyPositive ratioPositive
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall radiusSmall
    deformation control nonnegative small index
  have momentSmall := reference_normalized_signed_moment_small scales motion time index memoryNonnegative
    radiusPositive (differenceLower index) asymmetryBound normalizedSmall
  exact estimate evolution inside amplitudePositive frequencyBound ratioBound alphaPositive index (control index)
    (nonnegative index) (small index) memoryNonnegative boundNonnegative deformationBound lengthBound hessianBound
    (differenceLower index) asymmetryBound geometry.internalRadius geometry.internalSeparated geometry.sourceBounded
    geometry.receiverSmall geometry.sourceSmall geometry.centroidsSeparated momentSmall chartSmall

end EulerNonuniqueness.Paper
