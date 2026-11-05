import EulerNonuniqueness.General.ContinuousVectorSubmodule
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def continuousVectorAverage (action : ℝ → Space →L[ℝ] Space) (vector : Space) (step : ℝ) : Space :=
  step⁻¹ • ∫ parameter in (0 : ℝ)..step, action parameter vector

theorem continuousVectorAverage_tendsto (action : ℝ → Space →L[ℝ] Space)
    (identity : action 0 = ContinuousLinearMap.id ℝ Space) (vector : Space)
    (member : vector ∈ continuousVectorSubmodule action) :
    Tendsto (continuousVectorAverage action vector) (𝓝[≠] (0 : ℝ)) (𝓝 vector) := by
  have orbit : Continuous (fun parameter => action parameter vector) := member
  have derivative := intervalIntegral.integral_hasDerivAt_right (orbit.intervalIntegrable 0 0)
    orbit.aestronglyMeasurable.stronglyMeasurableAtFilter orbit.continuousAt
  simpa only [continuousVectorAverage, zero_add, intervalIntegral.integral_same, sub_zero, identity,
    ContinuousLinearMap.id_apply] using derivative.tendsto_slope_zero

theorem action_continuousVectorAverage (action : ℝ → Space →L[ℝ] Space)
    (addition : ∀ first second vector, action first (action second vector) = action (first + second) vector)
    (vector : Space) (member : vector ∈ continuousVectorSubmodule action) (step time : ℝ) :
    action time (continuousVectorAverage action vector step) =
      step⁻¹ • ((∫ parameter in (0 : ℝ)..(time + step), action parameter vector) -
        ∫ parameter in (0 : ℝ)..time, action parameter vector) := by
  have orbit : Continuous (fun parameter => action parameter vector) := member
  rw [continuousVectorAverage, map_smul]
  have integrable : IntervalIntegrable (fun parameter => action parameter vector) volume 0 step := orbit.intervalIntegrable _ _
  have commutation := (action time).intervalIntegral_comp_comm integrable
  rw [← commutation]
  have integrand : (fun parameter => action time (action parameter vector)) =
      fun parameter => action (parameter + time) vector := by
    funext parameter
    rw [addition, add_comm time parameter]
  rw [integrand]
  have shiftedIntegral := intervalIntegral.integral_comp_add_right
    (fun parameter => action parameter vector) (a := (0 : ℝ)) (b := step) time
  rw [shiftedIntegral]
  rw [zero_add, add_comm step time,
    intervalIntegral.integral_interval_sub_left (orbit.intervalIntegrable 0 (time + step)) (orbit.intervalIntegrable 0 time)]

theorem continuousVectorAverage_orbit_hasDerivAt (action : ℝ → Space →L[ℝ] Space)
    (addition : ∀ first second vector, action first (action second vector) = action (first + second) vector)
    (vector : Space) (member : vector ∈ continuousVectorSubmodule action) (step time : ℝ) :
    HasDerivAt (fun current => action current (continuousVectorAverage action vector step))
      (step⁻¹ • (action (time + step) vector - action time vector)) time := by
  have orbit : Continuous (fun parameter => action parameter vector) := member
  have primitiveDerivative (point : ℝ) :
      HasDerivAt (fun upper => ∫ parameter in (0 : ℝ)..upper, action parameter vector) (action point vector) point :=
    intervalIntegral.integral_hasDerivAt_right (orbit.intervalIntegrable 0 point)
      orbit.aestronglyMeasurable.stronglyMeasurableAtFilter orbit.continuousAt
  have shifted : HasDerivAt (fun current => ∫ parameter in (0 : ℝ)..(current + step), action parameter vector)
      (action (time + step) vector) time := by
    simpa only [one_smul] using (primitiveDerivative (time + step)).scomp time ((hasDerivAt_id time).add_const step)
  have equality : (fun current => action current (continuousVectorAverage action vector step)) =
      fun current => step⁻¹ • ((∫ parameter in (0 : ℝ)..(current + step), action parameter vector) -
        ∫ parameter in (0 : ℝ)..current, action parameter vector) := by
    funext current
    exact action_continuousVectorAverage action addition vector member step current
  rw [equality]
  exact HasDerivAt.const_smul step⁻¹ (shifted.sub (primitiveDerivative time))

theorem continuousVectorAverage_mem (action : ℝ → Space →L[ℝ] Space)
    (addition : ∀ first second vector, action first (action second vector) = action (first + second) vector)
    (vector : Space) (member : vector ∈ continuousVectorSubmodule action) (step : ℝ) :
    continuousVectorAverage action vector step ∈ continuousVectorSubmodule action := by
  apply continuous_iff_continuousAt.mpr
  intro time
  exact (continuousVectorAverage_orbit_hasDerivAt action addition vector member step time).continuousAt

end EulerNonuniqueness.General
