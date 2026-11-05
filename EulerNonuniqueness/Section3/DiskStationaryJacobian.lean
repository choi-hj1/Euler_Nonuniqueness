import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.General.LocalJacobianEquivalence

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryJacobianRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance stationaryJacobianOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance stationaryJacobianOperatorSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance stationaryJacobianOperatorRing : NormedRing
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedRing (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance stationaryJacobianOperatorAlgebra : NormedAlgebra ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAlgebra (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance stationaryJacobianUniformGroup : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance stationaryJacobianOperatorComplete : CompleteSpace
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.instCompleteSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)

theorem diskStationaryChart_eventually_jacobian_equivalence :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
      HasFDerivAt diskStationaryChart coordinates.toContinuousLinearMap increment ∧
      diskChartInverseDerivative increment = coordinates.symm.toContinuousLinearMap ∧
      HasFDerivAt diskChartInverseDerivative (fderiv ℝ diskChartInverseDerivative increment) increment := by
  have continuousDerivative : ContinuousAt (fderiv ℝ diskStationaryChart) (0 : PeriodicC1HolderHalf) :=
    (diskStationaryChart_analyticAt 0).fderiv.continuousAt
  let derivative : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskStationaryChart
  have invertible : IsUnit (fderiv ℝ diskStationaryChart (0 : PeriodicC1HolderHalf)) := by
    rw [diskStationaryChart_fderiv_zero]
    exact isUnit_one
  have nearby : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
      fderiv ℝ diskStationaryChart increment = coordinates.toContinuousLinearMap ∧
      diskChartInverseDerivative increment = coordinates.symm.toContinuousLinearMap := by
    unfold diskChartInverseDerivative
    with_reducible
      exact EulerNonuniqueness.General.eventually_jacobian_equivalence
        (Space := PeriodicC1HolderHalf) derivative 0 continuousDerivative invertible
  filter_upwards [nearby, diskChartInverseDerivative_analyticAt_zero.eventually_analyticAt] with increment actual inverseAnalytic
  obtain ⟨coordinates, derivativeIdentity, inverseIdentity⟩ := actual
  refine ⟨coordinates, ?_, inverseIdentity, inverseAnalytic.differentiableAt.hasFDerivAt⟩
  rw [← derivativeIdentity]
  exact (diskStationaryChart_analyticAt increment).differentiableAt.hasFDerivAt

end

end EulerNonuniqueness.Paper
