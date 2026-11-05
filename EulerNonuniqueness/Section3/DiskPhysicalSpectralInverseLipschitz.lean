import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseJacobian
import EulerNonuniqueness.General.LocalJacobianEquivalence
import EulerNonuniqueness.General.IdentityInverseContinuity
import EulerNonuniqueness.General.InverseOperatorLocalLipschitz

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralInverseLipschitzC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskPhysicalSpectralChart_hasStrictFDerivAt_zero :
    HasStrictFDerivAt diskPhysicalSpectralChart (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) 0 := by
  have outer : HasStrictFDerivAt diskStationaryChart (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf)
      (diskSpectralTubularChart 0) := by
    rw [diskSpectralTubularChart_zero]
    exact diskStationaryChart_hasStrictFDerivAt_zero
  have actual := outer.comp 0 diskSpectralTubularChart_hasStrictFDerivAt_zero
  simpa only [diskPhysicalSpectralChart, Function.comp_def, ContinuousLinearMap.id_comp] using actual

theorem diskPhysicalSpectralChart_eventually_inverse_jacobian :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point) =
        Ring.inverse (fderiv ℝ diskPhysicalSpectralChart point) := by
  have derivativeZero : fderiv ℝ diskPhysicalSpectralChart (0 : PeriodicC1HolderHalf) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    with_reducible
      exact diskPhysicalSpectralChart_hasStrictFDerivAt_zero.hasFDerivAt.fderiv
  have continuous : ContinuousAt (fderiv ℝ diskPhysicalSpectralChart) (0 : PeriodicC1HolderHalf) :=
    diskPhysicalSpectralChart_hasLipschitzDerivativeNear.2.continuousAt
  have invertible : IsUnit (fderiv ℝ diskPhysicalSpectralChart (0 : PeriodicC1HolderHalf)) := by
    rw [derivativeZero]
    exact isUnit_one
  let derivative : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskPhysicalSpectralChart
  have equivalents : ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        fderiv ℝ diskPhysicalSpectralChart point = coordinates.toContinuousLinearMap ∧
        Ring.inverse (fderiv ℝ diskPhysicalSpectralChart point) = coordinates.symm.toContinuousLinearMap := by
    with_reducible
      exact EulerNonuniqueness.General.eventually_jacobian_equivalence
        derivative 0 continuous invertible
  filter_upwards [equivalents, diskPhysicalSpectralChart_hasLipschitzDerivativeNear.1,
    diskPhysicalSpectralInverseDerivative_eventually_jacobian_identity]
    with point equivalent differentiable inverseIdentity
  obtain ⟨coordinates, derivativeIdentity, ringIdentity⟩ := equivalent
  have actual : HasFDerivAt diskPhysicalSpectralChart coordinates.toContinuousLinearMap point := by
    rw [← derivativeIdentity]
    exact differentiable.hasFDerivAt
  rw [inverseIdentity coordinates actual, ringIdentity]

theorem diskPhysicalSpectralInverseDerivative_chart_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear
      (fun point => diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point))
      (0 : PeriodicC1HolderHalf) := by
  have derivativeZero : fderiv ℝ diskPhysicalSpectralChart (0 : PeriodicC1HolderHalf) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    with_reducible
      exact diskPhysicalSpectralChart_hasStrictFDerivAt_zero.hasFDerivAt.fderiv
  have inverseRegular : EulerNonuniqueness.General.LipschitzNear
      (Ring.inverse : (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) →
        PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      (fderiv ℝ diskPhysicalSpectralChart 0) := by
    rw [derivativeZero]
    with_reducible
      exact EulerNonuniqueness.General.inverse_operator_lipschitzNear_identity
        (Space := PeriodicC1HolderHalf)
  have regular := inverseRegular.comp diskPhysicalSpectralChart_hasLipschitzDerivativeNear.2
  exact regular.congr diskPhysicalSpectralChart_eventually_inverse_jacobian

end EulerNonuniqueness.Paper
