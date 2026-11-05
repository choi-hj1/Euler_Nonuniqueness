import EulerNonuniqueness.Section3.ContourRotatingSelfMoments

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] areaCentroidNormalizationC1Group areaCentroidNormalizationC1Semi
  areaCentroidNormalizationC1Space forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourAreaCentroidNormalization_derivative_self (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (centeredSmall : ‖contourCentroidRecenter data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (normalizedSmall : ‖contourAreaCentroidNormalization data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    fderiv ℝ contourAreaCentroidNormalization data (diskEulerRotatingField data) =
      diskEulerRotatingField (contourAreaCentroidNormalization data) := by
  let velocity := diskEulerRotatingField data
  let line := fun time : ℝ => data + time • velocity
  have lineDerivative : HasDerivAt line velocity 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const velocity).const_add data
  have lineZero : line 0 = data := by simp [line]
  have positive := contourAreaFunctional_pos data (small.trans_le (min_le_left _ _))
  have areaDerivative : HasFDerivAt contourAreaFunctional (fderiv ℝ contourAreaFunctional data) (line 0) := by
    rw [lineZero]
    exact (analyticAt_contourAreaFunctional data).differentiableAt.hasFDerivAt
  have areaLine : HasDerivAt (fun time => contourAreaFunctional (line time)) 0 0 := by
    have chain := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℝ)
      (f := line) (0 : ℝ) areaDerivative lineDerivative
    simpa only [Function.comp_def, velocity, contourAreaFunctional_derivative_rotating_self data small] using chain
  have ratioLine : HasDerivAt (fun time => Real.pi / contourAreaFunctional (line time)) 0 0 := by
    have actual := (hasDerivAt_const (0 : ℝ) Real.pi).div areaLine (by simpa only [lineZero] using positive.ne')
    simpa only [zero_mul, mul_zero, sub_zero, zero_div] using actual
  have scaleLine : HasDerivAt (fun time => Real.sqrt (Real.pi / contourAreaFunctional (line time))) 0 0 := by
    have nonzero : Real.pi / contourAreaFunctional (line 0) ≠ 0 := by
      rw [lineZero]
      exact (div_pos Real.pi_pos positive).ne'
    simpa only [mul_zero, zero_div] using ratioLine.sqrt nonzero
  have centroidDerivative : HasFDerivAt contourCentroidFunctional (fderiv ℝ contourCentroidFunctional data) (line 0) := by
    rw [lineZero]
    exact (analyticAt_contourCentroidFunctional data (small.trans_le (min_le_left _ _))).differentiableAt.hasFDerivAt
  have centroidLine := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℂ)
    (f := line) (0 : ℝ) centroidDerivative lineDerivative
  have constantLine := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℂ) (E := PeriodicC1HolderHalf)
    (f := contourCentroidFunctional ∘ line) (0 : ℝ) c1ConstantCLM.hasFDerivAt centroidLine
  have recenteredLine : HasDerivAt (fun time => contourCentroidRecenter (line time))
      (velocity - c1ConstantCLM (fderiv ℝ contourCentroidFunctional data velocity)) 0 := by
    simpa only [Function.comp_def, contourCentroidRecenter] using lineDerivative.sub constantLine
  have normalizedLine : HasDerivAt (fun time => contourAreaCentroidNormalization (line time))
      (Real.sqrt (Real.pi / contourAreaFunctional data) •
        (velocity - c1ConstantCLM (fderiv ℝ contourCentroidFunctional data velocity))) 0 := by
    simpa only [contourAreaCentroidNormalization, lineZero, zero_smul, zero_add, add_zero] using scaleLine.smul recenteredLine
  have normalizationDerivative : HasFDerivAt contourAreaCentroidNormalization
      (fderiv ℝ contourAreaCentroidNormalization data) (line 0) := by
    rw [lineZero]
    exact (contourAreaCentroidNormalization_differentiableAt data (small.trans_le (min_le_left _ _))).hasFDerivAt
  have actual := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf)
    (f := line) (0 : ℝ) normalizationDerivative lineDerivative
  have derivativeValue := actual.unique normalizedLine
  have scalePositive : 0 < Real.sqrt (Real.pi / contourAreaFunctional data) :=
    Real.sqrt_pos.2 (div_pos Real.pi_pos positive)
  have covariance := diskEulerRotatingField_real_smul (contourCentroidRecenter data)
    (Real.sqrt (Real.pi / contourAreaFunctional data)) scalePositive.ne' centeredSmall normalizedSmall
  rw [diskEulerRotatingField_recenter data small centeredSmall] at covariance
  exact derivativeValue.trans covariance.symm

theorem contourAreaCentroidNormalization_eventually_derivative_self :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      fderiv ℝ contourAreaCentroidNormalization data (diskEulerRotatingField data) =
        diskEulerRotatingField (contourAreaCentroidNormalization data) := by
  filter_upwards [contourAreaCentroidNormalization_eventually_admissible] with data admissible
  exact contourAreaCentroidNormalization_derivative_self data admissible.1 admissible.2.2.1 admissible.2.2.2

end EulerNonuniqueness.Paper
