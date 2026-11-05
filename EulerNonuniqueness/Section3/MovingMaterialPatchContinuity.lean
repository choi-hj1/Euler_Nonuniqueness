import EulerNonuniqueness.Section3.MovingMaterialPatchMoments
import EulerNonuniqueness.Section3.MovingMaterialPatchMeasurability
import EulerNonuniqueness.Section3.IndicatorL1Continuity
import EulerNonuniqueness.Section3.SpacetimePatchContinuity
import EulerNonuniqueness.Section3.PolarArea

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem continuous_domain_spacetime_integral (path : MovingMaterialPatch)
    (function : ℝ × ℂ → ℝ) (functionContinuous : Continuous function) :
    Continuous (fun parameter => ∫ position in path.domain parameter, function (parameter, position)) := by
  let pulled := function ∘ movingSimilarityMap path.center path.phase path.radius
  have pulledContinuous : Continuous pulled := functionContinuous.comp
    (continuous_movingSimilarityMap path.center path.phase path.radius path.center_continuous path.phase_continuous)
  have result := (continuous_const : Continuous (fun _ : ℝ => path.radius ^ 2)).mul
    (continuous_nearCircleInterior_spacetime_integral path.shape path.shape_continuous path.nearby pulled pulledContinuous)
  convert result using 1
  funext parameter
  exact integral_similarityPatchDomain (path.center parameter) path.radius_positive (Circle.exp (path.phase parameter))
    (path.shape parameter) (path.nearby parameter) (fun position => function (parameter, position))

theorem domain_area_eq (path : MovingMaterialPatch) {first second : ℝ}
    (firstInside : first ∈ Ioo path.initialTime path.finalTime)
    (secondInside : second ∈ Ioo path.initialTime path.finalTime)
    (source : ℝ → Vorticity)
    (sourceIntegrable : ∀ time ∈ Ioo path.initialTime path.finalTime, Integrable (source time))
    (sourceMembership : ∀ time ∈ Ioo path.initialTime path.finalTime,
      MemLp (source time) (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ time ∈ Ioo path.initialTime path.finalTime, ∀ label,
      path.boundaryVelocity time label = biotSavart (source time) (path.boundary time label)) :
    volume.real (path.domain first) = volume.real (path.domain second) := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun time inside => (path.domain_area_hasDerivAt inside (sourceIntegrable time inside)
      (sourceMembership time inside) (material time inside)).differentiableAt.differentiableWithinAt)
    (fun time inside => (path.domain_area_hasDerivAt inside (sourceIntegrable time inside)
      (sourceMembership time inside) (material time inside)).deriv) firstInside secondInside

theorem domain_area_at_circle (path : MovingMaterialPatch) {time : ℝ}
    (circle : path.shape time = standardCircleBanach) :
    volume.real (path.domain time) = Real.pi * path.radius ^ 2 := by
  have result := integral_similarityPatchDomain (path.center time) path.radius_positive (Circle.exp (path.phase time))
    (path.shape time) (path.nearby time) (fun _ => (1 : ℝ))
  have normalizedArea : volume.real (nearCircleInterior (path.shape time) (path.nearby time)) = Real.pi := by
    rw [Measure.real, nearCircleInterior_area]
    simp_rw [circle]
    simp_rw [nearCircleRadialProfile_standardCircle]
    simp only [one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  simp only [setIntegral_const, smul_eq_mul, mul_one] at result
  change volume.real (path.domain time) = path.radius ^ 2 *
    volume.real (nearCircleInterior (path.shape time) (path.nearby time)) at result
  rw [normalizedArea, mul_comm] at result
  exact result

theorem tendsto_eLpNorm_domain_indicator_sub (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    (source : ℝ → Vorticity)
    (sourceIntegrable : ∀ parameter ∈ Ioo path.initialTime path.finalTime, Integrable (source parameter))
    (sourceMembership : ∀ parameter ∈ Ioo path.initialTime path.finalTime,
      MemLp (source parameter) (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ parameter ∈ Ioo path.initialTime path.finalTime, ∀ label,
      path.boundaryVelocity parameter label = biotSavart (source parameter) (path.boundary parameter label)) :
    Tendsto (fun parameter => eLpNorm
      ((path.domain parameter).indicator (fun _ => (1 : ℝ)) -
        (path.domain time).indicator (fun _ => (1 : ℝ))) 1 volume) (𝓝 time) (𝓝 0) := by
  have integrable (parameter : ℝ) : Integrable ((path.domain parameter).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff (path.domain_isOpen parameter).measurableSet).mpr
      (integrableOn_const.mpr (Or.inr (path.domain_isBounded parameter).measure_lt_top))
  have normConvergence := tendsto_integral_norm_indicator_sub_of_persistence path.domain time
    (fun parameter => (path.domain_isOpen parameter).measurableSet)
    (fun parameter => (path.domain_isBounded parameter).measure_lt_top.ne) (path.domain_persistence time)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds inside] with parameter member
      exact path.domain_area_eq member inside source sourceIntegrable sourceMembership material)
  have result := ENNReal.continuous_ofReal.continuousAt.tendsto.comp normConvergence
  simp only [ENNReal.ofReal_zero] at result
  convert result using 1
  funext parameter
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm
    ((integrable parameter).sub (integrable time))]
  rfl

end EulerNonuniqueness.Paper.MovingMaterialPatch
