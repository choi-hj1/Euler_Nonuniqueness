import EulerNonuniqueness.Section3.DiskSpectralFiberAlgebra
import EulerNonuniqueness.General.OperatorProjectionFiberEvaluation

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskSpectralTubularChart_eventually_fiber_derivative :
    ∀ᶠ neutral in 𝓝 (0 : PeriodicC1HolderHalf),
      diskRelabelNeutralCLM neutral = neutral → ∀ relative : PeriodicC1HolderHalf,
        diskRelabelNeutralCLM relative = 0 → ∀ direction : PeriodicC1HolderHalf,
        fderiv ℝ diskSpectralTubularChart (neutral + relative) direction =
          diskChartedSpectralCoordinates neutral direction +
            fderiv ℝ diskChartedSpectralCoordinates neutral direction relative := by
  filter_upwards [diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.1,
    diskChartedSpectralCoordinates_eventually_fixes_relabel] with neutral regular fixes fixed relative kernel direction
  have fixesLinear : (diskChartedSpectralCoordinates neutral).comp diskRelabelNeutralCLM = diskRelabelNeutralCLM := by
    apply ContinuousLinearMap.ext
    intro value
    exact fixes value
  unfold diskSpectralTubularChart
  with_reducible
    exact EulerNonuniqueness.General.spectralTubularChart_fderiv_fiber_apply
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      neutral relative direction diskChartedSpectralCoordinates_neutral_parameter fixed kernel regular fixesLinear

theorem diskSpectralTubularChart_eventually_fiber_linear_cancellation :
    ∀ᶠ neutral in 𝓝 (0 : PeriodicC1HolderHalf),
      diskRelabelNeutralCLM neutral = neutral → ∀ relative : PeriodicC1HolderHalf,
        diskRelabelNeutralCLM relative = 0 → ∀ direction : PeriodicC1HolderHalf,
        fderiv ℝ diskSpectralTubularChart (neutral + relative) (diskRotatingDerivative direction) =
          diskChartedSpectralCoordinates neutral (diskRotatingDerivative direction) := by
  filter_upwards [diskSpectralTubularChart_eventually_fiber_derivative,
    diskChartedSpectralCoordinates_eventually_derivative_annihilates_rotation]
    with neutral derivative annihilates fixed relative kernel direction
  rw [derivative fixed relative kernel]
  have killed := annihilates direction
  rw [fixed] at killed
  rw [killed]
  with_reducible simp only [ContinuousLinearMap.zero_apply, add_zero]

end

end EulerNonuniqueness.Paper
