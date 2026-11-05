import EulerNonuniqueness.Section3.DiskSpectralTubularChart
import EulerNonuniqueness.General.LocalJacobianEquivalence

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def diskSpectralTubularPartialHomeomorph : PartialHomeomorph PeriodicC1HolderHalf PeriodicC1HolderHalf :=
  diskSpectralTubularChart_hasStrictFDerivAt_zero.toPartialHomeomorph diskSpectralTubularChart
    (f' := ContinuousLinearEquiv.refl ℝ PeriodicC1HolderHalf)

theorem diskSpectralTubularPartialHomeomorph_zero_mem_source :
    (0 : PeriodicC1HolderHalf) ∈ diskSpectralTubularPartialHomeomorph.source :=
  diskSpectralTubularChart_hasStrictFDerivAt_zero.mem_toPartialHomeomorph_source

theorem diskSpectralTubularPartialHomeomorph_zero_mem_target :
    (0 : PeriodicC1HolderHalf) ∈ diskSpectralTubularPartialHomeomorph.target := by
  simpa only [diskSpectralTubularPartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe,
    diskSpectralTubularChart_zero] using diskSpectralTubularPartialHomeomorph.map_source
      diskSpectralTubularPartialHomeomorph_zero_mem_source

theorem diskSpectralTubularPartialHomeomorph_inverse_zero :
    diskSpectralTubularPartialHomeomorph.symm 0 = 0 := by
  simpa only [diskSpectralTubularPartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe,
    diskSpectralTubularChart_zero] using diskSpectralTubularPartialHomeomorph.left_inv
      diskSpectralTubularPartialHomeomorph_zero_mem_source

theorem diskSpectralTubularChart_eventually_jacobian_equivalence :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        HasFDerivAt diskSpectralTubularChart coordinates.toContinuousLinearMap increment ∧
        Ring.inverse (fderiv ℝ diskSpectralTubularChart increment) = coordinates.symm.toContinuousLinearMap := by
  have continuous : ContinuousAt (fderiv ℝ diskSpectralTubularChart) (0 : PeriodicC1HolderHalf) :=
    diskSpectralTubularChart_hasLipschitzDerivativeNear.2.continuousAt
  have derivativeZero : fderiv ℝ diskSpectralTubularChart (0 : PeriodicC1HolderHalf) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    with_reducible
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
        (HasStrictFDerivAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
          diskSpectralTubularChart_hasStrictFDerivAt_zero)
  have invertible : IsUnit (fderiv ℝ diskSpectralTubularChart (0 : PeriodicC1HolderHalf)) := by
    rw [derivativeZero]
    exact isUnit_one
  have nearby : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        fderiv ℝ diskSpectralTubularChart increment = coordinates.toContinuousLinearMap ∧
        Ring.inverse (fderiv ℝ diskSpectralTubularChart increment) = coordinates.symm.toContinuousLinearMap := by
    let derivative : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
      fderiv ℝ diskSpectralTubularChart
    with_reducible
      exact EulerNonuniqueness.General.eventually_jacobian_equivalence
        (Space := PeriodicC1HolderHalf) derivative 0 continuous invertible
  filter_upwards [nearby, diskSpectralTubularChart_hasLipschitzDerivativeNear.1] with increment equivalent regular
  obtain ⟨coordinates, identity, inverseIdentity⟩ := equivalent
  refine ⟨coordinates, ?_, inverseIdentity⟩
  rw [← identity]
  with_reducible exact regular.hasFDerivAt

end

end EulerNonuniqueness.Paper
