import EulerNonuniqueness.Section4.ReferenceComputedSaddleBound
import EulerNonuniqueness.Section5.ReferenceOutwardFaces

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem exists_uniform_computed_reference_face_radius :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
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
      |unstableShape motion time index| ≤ radius → |stableShape motion time index| ≤ radius →
      referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
        scales.omega (index.val + 1) * radius / 16 →
      (unstableShape motion time index = radius → scales.omega (index.val + 1) * radius / 2 ≤
        (referencePointShapeVelocity scales motion time index).1) ∧
      (unstableShape motion time index = -radius → (referencePointShapeVelocity scales motion time index).1 ≤
        -(scales.omega (index.val + 1) * radius / 2)) ∧
      (stableShape motion time index = radius → (referencePointShapeVelocity scales motion time index).2 ≤
        -(scales.omega (index.val + 1) * radius / 2)) ∧
      (stableShape motion time index = -radius → scales.omega (index.val + 1) * radius / 2 ≤
        (referencePointShapeVelocity scales motion time index).2) := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, quadratic, quadraticNonnegative,
    shapeRadius, shapeRadiusPositive, estimate⟩ := exists_uniform_computed_reference_saddle_bound
  let radius := min (min (shapeRadius / 4) (1 / (32 * (quadratic + 1)))) (1 / 8)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusSmall : radius ≤ 1 / 8 := min_le_right _ _
  have shapeSmall : radius ≤ shapeRadius / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have quadraticSmall : radius ≤ 1 / (32 * (quadratic + 1)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have scaled : 32 * (quadratic + 1) * radius ≤ 1 := by
    have divided := (le_div_iff₀ (by positivity : 0 < 32 * (quadratic + 1))).mp quadraticSmall
    nlinarith only [divided]
  have scalarCost : 4 * quadratic * radius ^ 2 ≤ radius / 8 := by
    have product := mul_le_mul_of_nonneg_right scaled radiusPositive.le
    nlinarith only [product, sq_nonneg radius]
  refine ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, radius, radiusPositive, radiusSmall, ?_⟩
  intro count scales motion horizon time deformation memory bound evolution inside amplitudePositive frequencyBound ratioBound
    alphaPositive index geometry control nonnegative small memoryNonnegative boundNonnegative deformationBound lengthBound
    hessianBound differenceLower differenceUpper asymmetryBound lengthSmall upper unstableBound stableBound forcingSmall
  have chartSmall : |unstableShape motion time index| + |stableShape motion time index| < shapeRadius := by
    linarith
  obtain ⟨rateLower, errorEstimate⟩ := estimate evolution inside amplitudePositive frequencyBound ratioBound alphaPositive
    index geometry control nonnegative small memoryNonnegative boundNonnegative deformationBound lengthBound hessianBound
    differenceLower differenceUpper asymmetryBound lengthSmall upper chartSmall
  have omegaPositive := scales.omega_pos (zero_lt_one.trans_le frequencyBound) (by linarith : 0 < scales.ratio) (index.val + 1)
  have numerical : 4 * (quadratic * scales.omega (index.val + 1)) * radius ^ 2 +
      2 * referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
      scales.omega (index.val + 1) * radius / 2 := by
    have multiplied := mul_le_mul_of_nonneg_left scalarCost omegaPositive.le
    nlinarith only [multiplied, forcingSmall, mul_pos omegaPositive radiusPositive]
  have faces := EulerNonuniqueness.Section5.reference_saddle_face_signs radiusPositive.le
    (mul_nonneg quadraticNonnegative omegaPositive.le) rateLower unstableBound stableBound errorEstimate numerical
  have unstableIdentity : referencePointShapeRate scales motion time index * unstableShape motion time index +
      ((referencePointShapeVelocity scales motion time index).1 -
        referencePointShapeRate scales motion time index * unstableShape motion time index) =
      (referencePointShapeVelocity scales motion time index).1 := by ring
  have stableIdentity : -referencePointShapeRate scales motion time index * stableShape motion time index +
      ((referencePointShapeVelocity scales motion time index).2 +
        referencePointShapeRate scales motion time index * stableShape motion time index) =
      (referencePointShapeVelocity scales motion time index).2 := by ring
  rwa [unstableIdentity, stableIdentity] at faces

end EulerNonuniqueness.Paper
