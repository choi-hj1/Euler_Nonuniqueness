import EulerNonuniqueness.Section3.ContourVelocitySecondFrechet
import EulerNonuniqueness.Section3.ContourVelocitySecondDerivativeIdentity
import EulerNonuniqueness.Section3.RelabeledDiskPeriodFamily

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabelDifferentiabilityC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance relabelDifferentiabilityC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance relabelDifferentiabilityOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance relabelDifferentiabilityOperatorModule : Module ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance relabelDifferentiabilityOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem relabeledDiskDerivative_hasDerivAt_actual_second_derivative (angular : PeriodicC1HolderHalf) :
    HasDerivAt (fun parameter : ℝ => relabeledDiskDerivative (parameter • angular))
      (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) standardCircleBanach
        (c1Product (Complex.I • angular) standardCircleBanach)) 0 := by
  have circleSmall : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have zero : ‖standardCircleBanach - standardCircleBanach‖ = 0 := by norm_num
    rw [zero]
    exact lt_min (by norm_num) (div_pos (by norm_num) (mul_pos (by norm_num) Real.pi_pos))
  have outer : HasFDerivAt (fun current => fderiv ℝ extendedContourVelocity current)
      (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) standardCircleBanach)
      (diskRelabelCurve angular 0) := by
    rw [diskRelabelCurve_zero]
    exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      (differentiableAt_fderiv_extendedContourVelocity standardCircleBanach circleSmall)
  have actual := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
    (E := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    (f := diskRelabelCurve angular) (f' := c1Product (Complex.I • angular) standardCircleBanach)
    (l := fun current => fderiv ℝ extendedContourVelocity current)
    (l' := fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) standardCircleBanach)
    (0 : ℝ) outer (diskRelabelCurve_first_jet angular)
  have subtracted := actual.sub_const (c1ProductCLM (c1Constant (Complex.I / 2)))
  have equality : (fun parameter : ℝ => relabeledDiskDerivative (parameter • angular)) =
      (fun parameter => fderiv ℝ extendedContourVelocity (diskRelabelCurve angular parameter) -
        c1ProductCLM (c1Constant (Complex.I / 2))) := by
    funext parameter
    rw [relabeledDiskDerivative, diskRelabelCurve_real_smul]
  rw [equality]
  exact subtracted

theorem relabeledDiskDerivative_hasDerivAt (angular : PeriodicC1HolderHalf)
    {radius : ℝ} (positive : 0 < radius) (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasDerivAt (fun parameter : ℝ => relabeledDiskDerivative (parameter • angular))
      ((2 : ℝ) • (contourVelocityBilinearCLM standardCircleBanach
        (innerRadius := 0) (outerRadius := radius) (by norm_num) positive small
        (by norm_num)) (c1Product (Complex.I • angular) standardCircleBanach)) 0 := by
  have actual := relabeledDiskDerivative_hasDerivAt_actual_second_derivative angular
  rw [fderiv_fderiv_extendedContourVelocity_eq standardCircleBanach
    (innerRadius := 0) (outerRadius := radius) (by norm_num) positive small
    (by norm_num)] at actual
  exact actual

end

end EulerNonuniqueness.Paper
