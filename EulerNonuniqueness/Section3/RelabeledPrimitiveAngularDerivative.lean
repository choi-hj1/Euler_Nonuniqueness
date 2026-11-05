import EulerNonuniqueness.Section3.RelabeledForcingPrimitiveSeries
import EulerNonuniqueness.Section3.RelabeledDiskForcingAnalytic
import EulerNonuniqueness.Section3.ExteriorSeriesFirstJetLipschitz
import EulerNonuniqueness.Section3.DiskForcingPhaseRotation

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

def relabeledPrimitiveAngularDerivative (frequency : ℝ) (amplitude : ℕ → ℝ → ℂ)
    (time : ℝ) (angular : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (exteriorContourPowerSeriesFirstJet (Circle.exp (frequency * time / 2))
    (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
    (diskRelabelCurve angular 1)).comp (fderiv ℝ (fun current => diskRelabelCurve current 1) angular)

theorem relabeledForcingPrimitiveSeries_eq_exterior_series
    (angular : PeriodicC1HolderHalf) (frequency : ℝ) (amplitude : ℕ → ℝ → ℂ) (time : ℝ) :
    relabeledForcingPrimitiveSeries angular frequency amplitude time =
      exteriorContourPowerSeries (Circle.exp (frequency * time / 2))
        (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
        (diskRelabelCurve angular 1) := by
  unfold relabeledForcingPrimitiveSeries exteriorContourPowerSeries
  apply tsum_congr
  intro degree
  unfold relabeledDiskForcingPrimitive rotatedExteriorPower relabeledDiskForcingMode
  rw [diskForcingPhase_eq_rotation_power]
  congr 1
  ring

theorem diskForcingPrimitiveFactor_norm_le {frequency : ℝ} (nonzero : frequency ≠ 0) (degree : ℕ) :
    ‖diskForcingPrimitiveFactor degree frequency‖ ≤ 2 / |frequency| := by
  rw [diskForcingPrimitiveFactor_norm]
  have denominator : |frequency| ≤ ((degree + 1 : ℕ) : ℝ) * |frequency| := by
    have degreeOne : (1 : ℝ) ≤ ((degree + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le degree)
    nlinarith [abs_nonneg frequency]
  exact div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr nonzero) denominator

theorem summable_relabeledPrimitiveCoefficient_weight96 {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    Summable (fun degree => (96 : ℝ) ^ (degree + 1) *
      ‖diskForcingPrimitiveFactor degree frequency * amplitude degree time‖) := by
  apply Summable.of_nonneg_of_le (fun degree => by positivity) (fun degree => ?_)
    (weighted.mul_left (2 / |frequency|))
  rw [norm_mul]
  have factor := mul_le_mul_of_nonneg_right (diskForcingPrimitiveFactor_norm_le nonzero degree)
    (norm_nonneg (amplitude degree time))
  have scaled := mul_le_mul_of_nonneg_left factor (show 0 ≤ (96 : ℝ) ^ (degree + 1) by positivity)
  exact scaled.trans_eq (by ring)

theorem relabeledForcingPrimitiveSeries_hasFDerivAt_angular
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (angular : PeriodicC1HolderHalf) (bounded : ‖diskRelabelCurve angular 1‖ < 3)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    HasFDerivAt (fun current => relabeledForcingPrimitiveSeries current frequency amplitude time)
      (relabeledPrimitiveAngularDerivative frequency amplitude time angular) angular := by
  have coefficients := summable_relabeledPrimitiveCoefficient_weight96 nonzero amplitude time weighted
  have outer := hasFDerivAt_exteriorContourPowerSeries (Circle.exp (frequency * time / 2))
    (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
    (diskRelabelCurve angular 1) bounded coefficients
  have inner := (diskRelabelMap_analyticAt angular).differentiableAt.hasFDerivAt
  have actual := outer.comp angular inner
  simpa only [Function.comp_def, ← relabeledForcingPrimitiveSeries_eq_exterior_series, relabeledPrimitiveAngularDerivative]
    using actual

theorem relabeledForcingPrimitiveSeries_hasDerivAt_moving_angular
    {frequency time : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ)
    {angular : ℝ → PeriodicC1HolderHalf} {velocity : PeriodicC1HolderHalf}
    (angularActual : HasDerivAt angular velocity time) (bounded : ‖diskRelabelCurve (angular time) 1‖ < 3)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    HasDerivAt (fun current => relabeledForcingPrimitiveSeries (angular current) frequency amplitude time)
      (relabeledPrimitiveAngularDerivative frequency amplitude time (angular time) velocity) time := by
  exact (relabeledForcingPrimitiveSeries_hasFDerivAt_angular nonzero amplitude time
    (angular time) bounded weighted).comp_hasDerivAt time angularActual

end EulerNonuniqueness.Paper
