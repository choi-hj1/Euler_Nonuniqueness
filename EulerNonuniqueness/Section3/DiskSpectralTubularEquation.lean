import EulerNonuniqueness.Section3.DiskSpectralTubularInverse

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

def diskSpectralTubularInverseDerivative (increment : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := Ring.inverse (fderiv ℝ diskSpectralTubularChart increment)

def diskSpectralTubularEulerField (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskSpectralTubularInverseDerivative increment (diskChartedEulerField (diskSpectralTubularChart increment))

theorem diskSpectralTubularChart_eventually_inverse_derivative :
    ∀ᶠ data in 𝓝 (0 : PeriodicC1HolderHalf),
      diskSpectralTubularChart (diskSpectralTubularPartialHomeomorph.symm data) = data ∧
      HasFDerivAt diskSpectralTubularPartialHomeomorph.symm
        (diskSpectralTubularInverseDerivative (diskSpectralTubularPartialHomeomorph.symm data)) data := by
  have inverseContinuous : Tendsto diskSpectralTubularPartialHomeomorph.symm
      (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [diskSpectralTubularPartialHomeomorph_inverse_zero] using
      (diskSpectralTubularPartialHomeomorph.symm.continuousAt diskSpectralTubularPartialHomeomorph_zero_mem_target).tendsto
  filter_upwards [diskSpectralTubularPartialHomeomorph.open_target.mem_nhds
      diskSpectralTubularPartialHomeomorph_zero_mem_target,
    inverseContinuous.eventually diskSpectralTubularChart_eventually_jacobian_equivalence] with data inTarget jacobian
  obtain ⟨coordinates, chartDerivative, inverseIdentity⟩ := jacobian
  refine ⟨diskSpectralTubularPartialHomeomorph.right_inv inTarget, ?_⟩
  unfold diskSpectralTubularInverseDerivative
  rw [inverseIdentity]
  have actualChartDerivative : HasFDerivAt
      (diskSpectralTubularPartialHomeomorph : PeriodicC1HolderHalf → PeriodicC1HolderHalf)
      coordinates.toContinuousLinearMap (diskSpectralTubularPartialHomeomorph.symm data) := by
    simpa only [diskSpectralTubularPartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe] using chartDerivative
  exact PartialHomeomorph.hasFDerivAt_symm (𝕜 := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) diskSpectralTubularPartialHomeomorph
    (f' := coordinates) (a := data) inTarget actualChartDerivative

theorem hasDerivAt_diskSpectralTubularChart_inverse_of_equation
    {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ} {external : PeriodicC1HolderHalf}
    (equation : HasDerivAt curve (frequency • diskChartedEulerField (curve time) + external) time)
    (rightInverse : diskSpectralTubularChart (diskSpectralTubularPartialHomeomorph.symm (curve time)) = curve time)
    (inverseDerivative : HasFDerivAt diskSpectralTubularPartialHomeomorph.symm
      (diskSpectralTubularInverseDerivative (diskSpectralTubularPartialHomeomorph.symm (curve time))) (curve time)) :
    HasDerivAt (fun current => diskSpectralTubularPartialHomeomorph.symm (curve current))
      (frequency • diskSpectralTubularEulerField (diskSpectralTubularPartialHomeomorph.symm (curve time)) +
        diskSpectralTubularInverseDerivative (diskSpectralTubularPartialHomeomorph.symm (curve time)) external) time := by
  have actual := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf)
    (E := PeriodicC1HolderHalf) time inverseDerivative equation
  have velocityIdentity :
      diskSpectralTubularInverseDerivative (diskSpectralTubularPartialHomeomorph.symm (curve time))
          (frequency • diskChartedEulerField (curve time) + external) =
        frequency • diskSpectralTubularEulerField (diskSpectralTubularPartialHomeomorph.symm (curve time)) +
          diskSpectralTubularInverseDerivative (diskSpectralTubularPartialHomeomorph.symm (curve time)) external := by
    rw [map_add, map_smul, diskSpectralTubularEulerField, rightInverse]
  simpa only [Function.comp_def, velocityIdentity] using actual

end

end EulerNonuniqueness.Paper
