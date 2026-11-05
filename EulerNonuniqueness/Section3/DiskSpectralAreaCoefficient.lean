import EulerNonuniqueness.Section3.DiskSpectralAreaDerivative
import EulerNonuniqueness.Section3.DiskStationaryAreaRemainder

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter MeasureTheory
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  stationaryAreaRemainderOperatorGroup stationaryAreaRemainderOperatorSpace

theorem diskRadialMeanCLM_standardCircle : diskRadialMeanCLM standardCircleBanach = 1 := by
  rw [diskRadialMeanCLM_apply]
  unfold diskRadialMean
  change (1 / (2 * Real.pi)) * (∫ label in (-Real.pi)..Real.pi,
    (star (standardCircle label) * standardCircle label).re) = 1
  have unit (label : ℝ) : star (standardCircle label) * standardCircle label = 1 := by
    rw [standardCircle_star_eq_inv]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num))
  simp_rw [unit, Complex.one_re]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  field_simp [Real.pi_ne_zero]
  ring

def diskSpectralAreaRadialCoefficient (increment : PeriodicC1HolderHalf) : ℝ :=
  fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM increment) standardCircleBanach

theorem diskSpectralAreaRadialCoefficient_zero : diskSpectralAreaRadialCoefficient 0 = 2 * Real.pi := by
  have derivative : fderiv ℝ diskSpectralTubularArea (0 : PeriodicC1HolderHalf) = (2 * Real.pi) • diskRadialMeanCLM := by
    with_reducible
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ) diskSpectralTubularArea_hasFDerivAt_zero
  unfold diskSpectralAreaRadialCoefficient
  rw [map_zero, derivative]
  change (2 * Real.pi) • diskRadialMeanCLM standardCircleBanach = 2 * Real.pi
  rw [diskRadialMeanCLM_standardCircle]
  exact mul_one _

theorem diskSpectralAreaRadialCoefficient_continuousAt_zero :
    ContinuousAt diskSpectralAreaRadialCoefficient (0 : PeriodicC1HolderHalf) := by
  have derivativeContinuous : ContinuousAt (fderiv ℝ diskSpectralTubularArea) (0 : PeriodicC1HolderHalf) :=
    diskSpectralTubularArea_hasLipschitzDerivativeNear.2.continuousAt
  have atNeutral : ContinuousAt (fderiv ℝ diskSpectralTubularArea)
      (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) := by simpa only [map_zero] using derivativeContinuous
  let evaluate : (PeriodicC1HolderHalf →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ standardCircleBanach
  unfold diskSpectralAreaRadialCoefficient
  exact evaluate.continuous.continuousAt.comp (atNeutral.comp diskRelabelNeutralCLM.continuous.continuousAt)

theorem diskSpectralAreaRadialCoefficient_eventually_positive :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), Real.pi ≤ diskSpectralAreaRadialCoefficient increment := by
  have limit := diskSpectralAreaRadialCoefficient_continuousAt_zero.tendsto
  rw [diskSpectralAreaRadialCoefficient_zero] at limit
  have nearby := limit.eventually (eventually_gt_nhds (by linarith [Real.pi_pos] : Real.pi < 2 * Real.pi))
  exact nearby.mono fun _ positive => positive.le

theorem diskSpectralTubularArea_eventually_neutral_value :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      diskSpectralTubularArea (diskRelabelNeutralCLM increment) = Real.pi := by
  have limit : Tendsto diskNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  have nearby := limit.eventually (Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [nearby] with increment inside
  have small : ‖diskNeutralCLM increment‖ < 1 / 2 := by
    have actual := Metric.mem_ball.mp inside
    have distance : dist (diskNeutralCLM increment) (0 : PeriodicC1HolderHalf) = ‖diskNeutralCLM increment‖ := by
      with_reducible exact dist_zero_right (diskNeutralCLM increment)
    rwa [distance] at actual
  unfold diskSpectralTubularArea diskStationaryArea
  rw [diskSpectralTubularChart_stationary, diskRelabelNeutralCLM_apply,
    diskStationaryChart_relabel _ (diskNeutralCLM_real increment),
    ← fixedRelabelEquivalence_circle _ small (diskNeutralCLM_real increment),
    contourAreaFunctional_fixedRelabel, contourAreaFunctional_standardCircle]

end

end EulerNonuniqueness.Paper
