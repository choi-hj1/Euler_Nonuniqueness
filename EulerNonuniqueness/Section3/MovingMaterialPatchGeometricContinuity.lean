import EulerNonuniqueness.Section3.MovingMaterialPatchContinuity
import EulerNonuniqueness.General.IndicatorL1AreaContinuity

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem continuous_domain_area (path : MovingMaterialPatch) :
    Continuous (fun time => volume.real (path.domain time)) := by
  have result := path.continuous_domain_spacetime_integral (fun _ => (1 : ℝ)) continuous_const
  simpa only [setIntegral_const, smul_eq_mul, mul_one, Measure.real] using result

theorem tendsto_eLpNorm_domain_indicator_sub_geometric (path : MovingMaterialPatch) (time : ℝ) :
    Tendsto (fun parameter => eLpNorm
      ((path.domain parameter).indicator (fun _ => (1 : ℝ)) -
        (path.domain time).indicator (fun _ => (1 : ℝ))) 1 volume) (𝓝 time) (𝓝 0) := by
  have integrable (parameter : ℝ) : Integrable ((path.domain parameter).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff (path.domain_isOpen parameter).measurableSet).mpr
      (integrableOn_const.mpr (Or.inr (path.domain_isBounded parameter).measure_lt_top))
  have normConvergence := tendsto_integral_norm_indicator_sub_of_persistence_of_area_tendsto volume path.domain time
    (fun parameter => (path.domain_isOpen parameter).measurableSet)
    (fun parameter => (path.domain_isBounded parameter).measure_lt_top.ne) (path.domain_persistence time)
    path.continuous_domain_area.continuousAt.tendsto
  have result := ENNReal.continuous_ofReal.continuousAt.tendsto.comp normConvergence
  simp only [ENNReal.ofReal_zero] at result
  convert result using 1
  funext parameter
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm
    ((integrable parameter).sub (integrable time))]
  rfl

end EulerNonuniqueness.Paper.MovingMaterialPatch
