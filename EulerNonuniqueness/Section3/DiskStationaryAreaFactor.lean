import EulerNonuniqueness.Section3.DiskStationaryAreaRemainder

namespace EulerNonuniqueness.Paper

noncomputable section

open Set Metric

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryAreaFactorHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance stationaryAreaFactorC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance stationaryAreaFactorOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

theorem diskStationaryArea_exists_factored_mean_bound :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ angular : PeriodicC1HolderHalf,
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ transverse : PeriodicC1HolderHalf,
      ‖diskMaterialPerturbation 0 angular‖ + ‖transverse‖ ≤ radius →
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3 →
      diskStationaryArea (diskMaterialPerturbation 0 angular + transverse) = Real.pi →
      |diskRadialMean (diskMaterialPerturbation 0 angular + transverse)| ≤
        constant * (‖diskMaterialPerturbation 0 angular‖ + ‖transverse‖) * ‖transverse‖ := by
  obtain ⟨radius, positive, constant, nonnegative, actualDerivative, derivativeBound⟩ :=
    diskStationaryAreaRemainder_exists_derivative_bound
  refine ⟨radius, positive, constant / (2 * Real.pi), by positivity, ?_⟩
  intro angular realValues transverse inside small area
  let derivative : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] ℝ := fderiv ℝ diskStationaryAreaRemainder
  have powerBound : ∀ value ∈ closedBall (0 : PeriodicC1HolderHalf) radius,
      ‖fderiv ℝ diskStationaryAreaRemainder value‖ ≤ constant * ‖value‖ ^ 1 := by
    simpa only [pow_one] using derivativeBound
  have factored : ‖diskStationaryAreaRemainder (diskMaterialPerturbation 0 angular + transverse)‖ ≤
      constant * (‖diskMaterialPerturbation 0 angular‖ + ‖transverse‖) ^ 1 * ‖transverse‖ := by
    with_reducible
      exact EulerNonuniqueness.General.stationary_remainder_transverse_power_factor
        (Domain := PeriodicC1HolderHalf) (Range := ℝ) diskStationaryAreaRemainder
        derivative 1 nonnegative actualDerivative powerBound
        (diskMaterialPerturbation 0 angular) transverse inside
        (diskStationaryAreaRemainder_relabel angular realValues small)
  have normalized : (2 * Real.pi) * |diskRadialMean (diskMaterialPerturbation 0 angular + transverse)| ≤
      constant * (‖diskMaterialPerturbation 0 angular‖ + ‖transverse‖) * ‖transverse‖ := by
    simpa only [diskStationaryAreaRemainder, area, sub_self, ContinuousLinearMap.smul_apply,
      diskRadialMeanCLM_apply, smul_eq_mul, zero_sub, Real.norm_eq_abs, abs_neg, abs_mul,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), pow_one] using factored
  have divided : |diskRadialMean (diskMaterialPerturbation 0 angular + transverse)| ≤
      (constant * (‖diskMaterialPerturbation 0 angular‖ + ‖transverse‖) * ‖transverse‖) / (2 * Real.pi) :=
    (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by nlinarith [normalized])
  convert divided using 1 <;> ring

end

end EulerNonuniqueness.Paper
