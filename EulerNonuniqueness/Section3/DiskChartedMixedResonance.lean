import EulerNonuniqueness.Section3.DiskChartedQuadraticBilinear
import EulerNonuniqueness.Section3.DiskChartedRelabelPeriodFamily
import EulerNonuniqueness.Section3.DiskPhysicalExponentialAllTimes
import EulerNonuniqueness.General.LocalExponentialGroupMixedCancellation

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance chartedMixedHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd chartedBilinearOperatorGroup
  chartedBilinearOperatorModule chartedBilinearOperatorSpace chartedBilinearOperatorUniformAdd
  chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

theorem diskChartedQuadraticResonance_relabel_input_zero
    (angular direction : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
      diskPhysicalGroup (4 * Real.pi) diskChartedQuadraticBilinear
      (diskMaterialPerturbation 0 angular) direction = 0 := by
  let neutral : PeriodicC1HolderHalf := diskMaterialPerturbation 0 angular
  let operator : ℝ → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fun scalar => fderiv ℝ diskChartedEulerField (scalar • neutral)
  obtain ⟨radius, positive, continuousOperator⟩ := diskChartedDerivativeLine_exists_continuousOn neutral
  have actualDerivative : HasDerivAt operator ((2 : ℝ) • diskChartedQuadraticBilinear neutral) 0 :=
    by
      with_reducible exact diskChartedDerivativeLine_hasDerivAt neutral
  have period : ∀ᶠ scalar in 𝓝 (0 : ℝ),
      EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
        (operator scalar) (4 * Real.pi) = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf :=
    diskChartedEulerField_relabel_eventually_exp_period angular realValues
  have kernel : operator 0 neutral = 0 := by
    change fderiv ℝ diskChartedEulerField ((0 : ℝ) • neutral) neutral = 0
    rw [zero_smul, diskChartedEulerField_fderiv_zero]
    change diskRotatingDerivative (diskMaterialPerturbation 0 angular) = 0
    rw [← diskRelabel_tangent_eq_material angular]
    exact diskRotatingDerivative_relabel_tangent_zero angular realValues
  have actual : EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
      (EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf) (operator 0))
      (4 * Real.pi) diskChartedQuadraticBilinear neutral direction = 0 := by
    with_reducible
      exact EulerNonuniqueness.General.localExponentialGroup_mixed_resonance_zero
        (Space := PeriodicC1HolderHalf) operator diskChartedQuadraticBilinear neutral positive
        (by positivity : 0 < 4 * Real.pi) continuousOperator actualDerivative period kernel direction
  have operatorZero : operator 0 = diskRotatingDerivative := by
    change fderiv ℝ diskChartedEulerField ((0 : ℝ) • neutral) = diskRotatingDerivative
    rw [zero_smul, diskChartedEulerField_fderiv_zero]
  rw [operatorZero] at actual
  have groupIdentity : EulerNonuniqueness.General.linearExponentialGroup
      (Space := PeriodicC1HolderHalf) diskRotatingDerivative = diskPhysicalGroup := by
    funext time
    with_reducible exact (diskPhysicalGroup_eq_exponential_all_times time).symm
  rw [groupIdentity] at actual
  exact actual

end

end EulerNonuniqueness.Paper
