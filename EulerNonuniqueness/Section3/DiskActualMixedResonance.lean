import EulerNonuniqueness.Section3.RelabeledDiskDerivativeDifferentiability
import EulerNonuniqueness.Section3.RelabeledDiskDerivativeContinuity
import EulerNonuniqueness.Section3.DiskPhysicalExponentialAllTimes
import EulerNonuniqueness.General.LocalExponentialGroupMixedCancellation

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance actualMixedHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
attribute [local instance] relabelDifferentiabilityC1Space relabelDifferentiabilityC1ContinuousAdd
  relabelDifferentiabilityOperatorGroup relabelDifferentiabilityOperatorModule relabelDifferentiabilityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd secondIdentityBilinearGroup secondIdentityBilinearModule

theorem diskActualQuadraticResonance_relabel_input_zero
    {radius : ℝ} (positive : 0 < radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (angular direction : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
      diskPhysicalGroup (4 * Real.pi)
      (contourVelocityBilinearCLM standardCircleBanach (innerRadius := 0) (outerRadius := radius)
        (by norm_num) positive small (by simp))
      (diskMaterialPerturbation 0 angular) direction = 0 := by
  let bilinear : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    contourVelocityBilinearCLM standardCircleBanach (innerRadius := 0) (outerRadius := radius)
      (by norm_num) positive small (by simp)
  let neutral : PeriodicC1HolderHalf := c1Product (Complex.I • angular) standardCircleBanach
  obtain ⟨parameterRadius, parameterPositive, continuousOperator⟩ :=
    relabeledDiskDerivative_exists_continuousOn angular
  have actualDerivative : HasDerivAt (fun parameter : ℝ => relabeledDiskDerivative (parameter • angular))
      ((2 : ℝ) • bilinear neutral) 0 := by
    with_reducible
      exact relabeledDiskDerivative_hasDerivAt angular positive small
  have period := relabeledDiskDerivative_eventually_exp_period angular realValues
  have kernel : relabeledDiskDerivative ((0 : ℝ) • angular) neutral = 0 := by
    rw [zero_smul, relabeledDiskDerivative_zero]
    exact diskRotatingDerivative_relabel_tangent_zero angular realValues
  have actual : EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
      (EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
        (relabeledDiskDerivative ((0 : ℝ) • angular)))
      (4 * Real.pi) bilinear neutral direction = 0 := by
    with_reducible
      exact EulerNonuniqueness.General.localExponentialGroup_mixed_resonance_zero
        (Space := PeriodicC1HolderHalf) (fun parameter : ℝ => relabeledDiskDerivative (parameter • angular))
        bilinear neutral parameterPositive (by positivity : 0 < 4 * Real.pi)
        continuousOperator actualDerivative period kernel direction
  simp only [zero_smul, relabeledDiskDerivative_zero] at actual
  change EulerNonuniqueness.General.quadraticResonance
    (EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf) diskRotatingDerivative)
    (4 * Real.pi) bilinear neutral direction = 0 at actual
  have groupIdentity : EulerNonuniqueness.General.linearExponentialGroup
      (Space := PeriodicC1HolderHalf) diskRotatingDerivative = diskPhysicalGroup := by
    funext time
    with_reducible exact (diskPhysicalGroup_eq_exponential_all_times time).symm
  rw [groupIdentity] at actual
  have neutralIdentity : neutral = diskMaterialPerturbation 0 angular := diskRelabel_tangent_eq_material angular
  rw [neutralIdentity] at actual
  exact actual

end

end EulerNonuniqueness.Paper
