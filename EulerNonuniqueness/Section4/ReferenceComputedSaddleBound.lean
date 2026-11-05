import EulerNonuniqueness.Section4.ReferenceComputedShapeEquation
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section4.ReferenceUniformShapeForcing
import EulerNonuniqueness.Section4.ReferenceNeutralNormalization
import EulerNonuniqueness.Section4.ReferenceSaddleVelocity

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

def referenceShapeForcingBudget (scales : Scales) (index : ℕ) (internal memory bound : ℝ) : ℝ :=
  ((2 * internal * memory ^ 2 + 27648) / Real.pi) * scales.strain +
    ((414720000000 + 3397386240 / Real.pi) * bound / scales.amplitude) / scales.omega index ^ 4

def referencePointShapeRate {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ :=
  2 * Real.sqrt 2 * (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
    diagonalDifference motion time index)

theorem exists_uniform_computed_reference_saddle_bound :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ),
      ∃ quadratic ≥ (0 : ℝ), ∃ shapeRadius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation memory bound : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (index : Fin count), ReferenceCentroidFieldGeometry scales motion time index →
      (∀ patch, BoundaryCloseToCircle scales motion time index patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
      deformation ≤ bound / scales.omega (index.val + 1) ^ 2 →
      scales.length (index.val + 1) ≤ 1 → scales.hessian ≤ 1 →
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index →
      diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2 →
      ‖centroidAsymmetry motion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
      scales.length (index.val + 1) < momentRadius / (8 * (memory + 1)) →
      0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im →
      |unstableShape motion time index| + |stableShape motion time index| < shapeRadius →
      scales.omega (index.val + 1) ≤ referencePointShapeRate scales motion time index ∧
        |(referencePointShapeVelocity scales motion time index).1 -
            referencePointShapeRate scales motion time index * unstableShape motion time index| +
          |(referencePointShapeVelocity scales motion time index).2 +
            referencePointShapeRate scales motion time index * stableShape motion time index| ≤
          quadratic * scales.omega (index.val + 1) *
              (|unstableShape motion time index| + |stableShape motion time index|) ^ 2 +
            2 * referenceShapeForcingBudget scales (index.val + 1) internal memory bound := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, forcingEstimate⟩ :=
    exists_uniform_reference_shape_forcing_bound
  obtain ⟨quadratic, quadraticNonnegative, shapeRadius, shapeRadiusPositive, saddleEstimate⟩ :=
    exists_uniform_reference_saddle_velocity_bound
  refine ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, quadratic, quadraticNonnegative,
    min shapeRadius (1 / 4), lt_min shapeRadiusPositive (by norm_num), ?_⟩
  intro count scales motion horizon time deformation memory bound evolution inside amplitudePositive frequencyBound
    ratioBound alphaPositive index geometry control nonnegative small memoryNonnegative boundNonnegative deformationBound
    lengthBound hessianBound differenceLower differenceUpper asymmetryBound lengthSmall upper chartSmall
  have paper := pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have coherentSmall : |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4 := by
    rw [paper]
    exact chartSmall.le.trans (min_le_right _ _)
  have momentSmall := reference_normalized_signed_moment_small scales motion time index memoryNonnegative
    momentRadiusPositive differenceLower asymmetryBound lengthSmall
  have forcing := forcingEstimate evolution inside amplitudePositive frequencyBound ratioBound alphaPositive index control
    nonnegative small memoryNonnegative boundNonnegative deformationBound lengthBound hessianBound differenceLower
    asymmetryBound geometry.internalRadius geometry.internalSeparated geometry.sourceBounded geometry.receiverSmall
    geometry.sourceSmall geometry.centroidsSeparated momentSmall coherentSmall
  change ‖referencePointShapeForcing scales motion time index‖ ≤
    referenceShapeForcingBudget scales (index.val + 1) internal memory bound at forcing
  exact saddleEstimate (referencePointShapeForcing scales motion time index)
    (scales.omega_pos (zero_lt_one.trans_le frequencyBound) (by linarith) _) (scales.length_pos _)
    differenceLower differenceUpper (chartSmall.trans_le (min_le_left _ _)) forcing

end EulerNonuniqueness.Paper
