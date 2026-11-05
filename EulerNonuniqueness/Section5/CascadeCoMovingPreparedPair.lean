import EulerNonuniqueness.Section5.CascadeControlledInitialMonitors
import EulerNonuniqueness.Section5.CascadeCoMovingAnalyticBootstrap

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

structure CascadeCoMovingPreparedPair (scales : Scales) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    (phase dipoleAngle : ℕ → ℝ) (threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ)
    (count : ℕ) where
  reference : PatchMotion count
  unstable : Fin count → ℝ
  referenceSolution : ReferenceSolution scales reference (fun index => phase (index.val + 1)) threshold referenceConstant
  referenceInitial : ReferenceInitialDisks scales reference (fun index => phase (index.val + 1)) unstable threshold
  configuration : FiniteContourConfiguration (count * 4)
  densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
    patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)
  gap : ℝ
  gapPositive : 0 < gap
  margin : ℝ
  marginPositive : 0 < margin
  marginShape : margin ≤ shapeRadius / 8
  marginUnit : margin ≤ 1 / 8
  marginSlack : ∀ first second : Fin count × Fin 4,
    gap + 4 * margin ≤ 4 * cascadePairCutoffSlack scales factor first second
  trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3
    (0, (fun label => cascadeInitialCenter scales orbit sectionTime (fun index => phase (index.val + 1)) unstable
      (dipoleAngle count) (finProdFinEquiv.symm label)), fun _ => standardCircleBanach)
  commonInitial : CascadeInitialDisks scales orbit sectionTime dipoleAngle reference trajectory.movingFamily.patchMotion
  initialMargin : 2 * margin ≤ infDist (trajectory.curve 0) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ
  initialInternal : ∀ receiver source, cascadeInternalGapMonitor scales factor receiver source
    (fun label => (trajectory.curve 0).2.1 (finProdFinEquiv label)) < 0
  initialLocation : ∀ label, cascadeLocationMonitor scales label
    (fun label => (trajectory.curve 0).2.1 (finProdFinEquiv label)) < 0
  continuousVectors : ∀ time ∈ Ico (0 : ℝ) 3,
    trajectory.curve time ∈ movingContinuousContourSubmodule (count * 4)
  analyticControl : ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ 1 →
    (∀ time ∈ Icc 0 terminal, ∀ receiver source,
      cascadeInternalGapMonitor scales factor receiver source (trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 terminal, ∀ label,
      cascadeExtentMonitor scales label (trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 terminal, ∀ first second,
      cascadeAnchorLowerMonitor scales first second (trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 terminal, ∀ index,
      cascadeAnchorNormMonitor index (trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    FinitePatchEvolution scales trajectory.movingFamily.patchMotion terminal ∧
    ∀ time ∈ Icc 0 terminal,
      margin < infDist (trajectory.curve time) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ ∧
      (∀ label, ‖(trajectory.curve time).2.2 label - standardCircleBanach‖ < min (monitor / 2) (shapeRadius / 2)) ∧
      ∀ index patch, BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion time index patch
        (boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2))

end EulerNonuniqueness.Paper

