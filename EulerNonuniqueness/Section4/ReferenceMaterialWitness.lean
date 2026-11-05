import EulerNonuniqueness.Section4.ReferenceControlledShootingFamilies
import EulerNonuniqueness.Section3.MovingCentroidGaugeEuler

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

structure ReferenceMaterialCoarseWitness (scales : Scales) {count : ℕ}
    (phase : Fin count → ℝ) (threshold constant : ℝ) where
  unstable : Fin count → ℝ
  configuration : FiniteContourConfiguration (count * 4)
  densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
    patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)
  shapeRadius : ℝ
  shapePositive : 0 < shapeRadius
  shapeSmall : shapeRadius < min (1 / 3) (2 / (3 * Real.pi))
  gap : ℝ
  margin : ℝ
  marginPositive : 0 < margin
  trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3
    (referenceMechanicalInitialState scales phase unstable)
  initial : ReferenceInitialDisks scales trajectory.movingFamily.patchMotion phase unstable threshold
  evolution : FinitePatchEvolution scales trajectory.movingFamily.patchMotion 2
  coarse : ReferenceCoarseBounds scales trajectory.movingFamily.patchMotion threshold constant
  safe : ∀ time ∈ Icc (0 : ℝ) 2, margin ≤ infDist (trajectory.curve time)
    (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ
  continuousVectors : ∀ time ∈ Icc (0 : ℝ) 2, ∀ label,
    (trajectory.curve time).2.2 label ∈ contourContinuousVectorSubmodule

end EulerNonuniqueness.Paper
