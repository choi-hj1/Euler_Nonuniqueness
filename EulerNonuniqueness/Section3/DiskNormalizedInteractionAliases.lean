import EulerNonuniqueness.Section3.CanonicalForcingContinuityModel

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

def diskNormalizedInteractionCurve (frequency : ℝ) (curve : ℝ → PeriodicC1HolderHalf)
    (time : ℝ) : PeriodicC1HolderHalf :=
  diskPhysicalScaledGroup frequency (-time) (diskNormalizedQuadraticObservable (curve time))

def diskNormalizedInteractionNormCurve (frequency : ℝ) (curve : ℝ → PeriodicC1HolderHalf) : ℝ → ℝ :=
  fun time => ‖diskNormalizedInteractionCurve frequency curve time‖

def diskNormalizedCubicRate (frequency : ℝ) (data : PeriodicC1HolderHalf) : ℝ :=
  |frequency| * ‖diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate data)‖ ^ 3

theorem diskNormalizedInteractionCurve_exists_uniform_continuity :
    ∃ radius > 0, ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ},
      ‖curve time - standardCircleBanach‖ ≤ radius → ContinuousAt curve time →
      ContinuousAt (diskNormalizedInteractionCurve frequency curve) time := by
  unfold diskNormalizedInteractionCurve
  with_reducible_and_instances
    exact diskNormalizedInteraction_exists_uniform_canonical_continuity

theorem diskNormalizedInteractionCurve_exists_uniform_error_slope :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency errorConstant first second third : ℝ}
        {error : PeriodicC1HolderHalf},
      1 ≤ errorConstant → ‖curve time - standardCircleBanach‖ ≤ radius →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) + error) time →
      ‖error‖ ≤ errorConstant * (first + second + third) →
      ∀ threshold, (constant * errorConstant) *
        (diskNormalizedCubicRate frequency (curve time) + first + second + third) < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (diskNormalizedInteractionNormCurve frequency curve) time later < threshold := by
  unfold diskNormalizedCubicRate diskNormalizedInteractionNormCurve diskNormalizedInteractionCurve
  with_reducible_and_instances
    exact diskNormalizedQuadraticObservable_exists_uniform_canonical_error_slope

end EulerNonuniqueness.Paper
