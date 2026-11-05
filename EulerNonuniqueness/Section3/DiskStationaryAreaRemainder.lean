import EulerNonuniqueness.Section3.DiskStationaryArea
import EulerNonuniqueness.General.FlatDerivativeBound
import EulerNonuniqueness.General.StationaryPowerFactor

namespace EulerNonuniqueness.Paper

noncomputable section

open Set Metric

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryAreaRemainderHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance stationaryAreaRemainderC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance stationaryAreaRemainderOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance stationaryAreaRemainderOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

def diskStationaryAreaRemainder (increment : PeriodicC1HolderHalf) : ℝ :=
  diskStationaryArea increment - Real.pi - (((2 * Real.pi) • diskRadialMeanCLM) increment)

theorem diskStationaryAreaRemainder_analyticAt (increment : PeriodicC1HolderHalf) :
    AnalyticAt ℝ diskStationaryAreaRemainder increment := by
  exact ((diskStationaryArea_analyticAt increment).sub analyticAt_const).sub
    (((2 * Real.pi) • diskRadialMeanCLM).analyticAt (x := increment))

theorem diskStationaryAreaRemainder_hasFDerivAt_zero :
    HasFDerivAt diskStationaryAreaRemainder (0 : PeriodicC1HolderHalf →L[ℝ] ℝ) 0 := by
  let linear : PeriodicC1HolderHalf →L[ℝ] ℝ := (2 * Real.pi) • diskRadialMeanCLM
  have linearDerivative : HasFDerivAt (fun value : PeriodicC1HolderHalf => linear value) linear
      (0 : PeriodicC1HolderHalf) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ) linear
      (x := (0 : PeriodicC1HolderHalf))
  have shifted : HasFDerivAt (fun value : PeriodicC1HolderHalf => diskStationaryArea value - Real.pi)
      linear (0 : PeriodicC1HolderHalf) :=
    HasFDerivAt.sub_const (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ)
      Real.pi diskStationaryArea_hasFDerivAt_zero
  have actual := HasFDerivAt.sub (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ) shifted linearDerivative
  have zeroLinear : linear - linear = (0 : PeriodicC1HolderHalf →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro value
    change linear value - linear value = 0
    exact sub_self _
  change HasFDerivAt (fun value => diskStationaryArea value - Real.pi - linear value)
    (linear - linear) (0 : PeriodicC1HolderHalf) at actual
  rw [zeroLinear] at actual
  exact actual

theorem diskStationaryAreaRemainder_relabel (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3) :
    diskStationaryAreaRemainder (diskMaterialPerturbation 0 angular) = 0 := by
  unfold diskStationaryAreaRemainder
  rw [diskStationaryArea_relabel angular realValues small, ContinuousLinearMap.smul_apply,
    diskRadialMeanCLM_apply, diskRadialMean_relabel_tangent angular realValues]
  simp only [sub_self, smul_zero, sub_zero]

theorem diskStationaryAreaRemainder_exists_derivative_bound :
    ∃ radius > 0, ∃ constant ≥ 0,
      (∀ value ∈ closedBall (0 : PeriodicC1HolderHalf) radius,
        HasFDerivAt diskStationaryAreaRemainder (fderiv ℝ diskStationaryAreaRemainder value) value) ∧
      ∀ value ∈ closedBall (0 : PeriodicC1HolderHalf) radius,
        ‖fderiv ℝ diskStationaryAreaRemainder value‖ ≤ constant * ‖value‖ := by
  have smooth : ContDiff ℝ 2 diskStationaryAreaRemainder :=
    contDiff_iff_contDiffAt.mpr (fun value => (diskStationaryAreaRemainder_analyticAt value).contDiffAt)
  have flat : fderiv ℝ diskStationaryAreaRemainder (0 : PeriodicC1HolderHalf) = 0 :=
    HasFDerivAt.fderiv (E := PeriodicC1HolderHalf) (F := ℝ) diskStationaryAreaRemainder_hasFDerivAt_zero
  with_reducible
    exact EulerNonuniqueness.General.exists_local_derivative_linear_bound_of_contDiff_two
      (Domain := PeriodicC1HolderHalf) (Range := ℝ) diskStationaryAreaRemainder smooth flat

end

end EulerNonuniqueness.Paper
