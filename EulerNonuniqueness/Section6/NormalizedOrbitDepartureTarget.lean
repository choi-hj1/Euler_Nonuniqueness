import EulerNonuniqueness.Section6.NormalizedOrbitChartEntry
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem normalizedSeparatingOrbit_eventually_positive_unstable
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∀ᶠ time : ℝ in atBot, 0 < orbitUnstableShape orbit time := by
  have asymptotic := normalized.2.2.2.2.2.1
  have positive := asymptotic.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [positive] with time positive
  exact (mul_pos_iff.mp positive).resolve_right (by
    intro negative
    exact (not_lt_of_gt (Real.exp_pos _)) negative.1) |>.2

theorem normalizedSeparatingOrbit_eventually_positive_coordinate
    {coordinate : ℝ → ℝ} (coordinateZero : coordinate 0 = 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∀ᶠ time : ℝ in atBot, 0 < coordinate (orbitUnstableShape orbit time) := by
  have unstableLimit := continuous_fst.continuousAt.tendsto.comp
    (normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized)
  have positive := normalizedSeparatingOrbit_eventually_positive_unstable orbit normalized
  have rightLimit : Tendsto (orbitUnstableShape orbit) atBot (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨unstableLimit, positive⟩
  have slopePositive := (coordinateDerivative.tendsto_slope_zero_right.comp rightLimit).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [positive, slopePositive] with time positive slopePositive
  simp only [zero_add, coordinateZero, sub_zero, smul_eq_mul] at slopePositive
  exact (mul_pos_iff.mp slopePositive).resolve_right (by
    intro negative
    exact (not_lt_of_gt (inv_pos.mpr positive)) negative.1) |>.2

theorem normalizedSeparatingOrbit_normalForm_departure_target
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape orbit time = graph (orbitUnstableShape orbit time))
    {accuracy : ℝ} (accuracyPositive : 0 < accuracy) :
    ∃ incomingTime : ℝ, ∃ target > (0 : ℝ), ∃ radius > (0 : ℝ), ∃ tolerance > (0 : ℝ),
      target = coordinate (orbitUnstableShape orbit incomingTime) ∧
      target < accuracy ∧
      orbitStableShape orbit incomingTime = graph (orbitUnstableShape orbit incomingTime) ∧
      ∀ point : ℝ × ℝ, |point.1| + |point.2| < radius →
        |coordinate point.1 - target| + |point.2 - graph point.1| < tolerance →
        |point.1 - orbitUnstableShape orbit incomingTime| +
          |point.2 - orbitStableShape orbit incomingTime| < accuracy := by
  obtain ⟨radius, radiusPositive, constant, constantOne, entry⟩ :=
    normalizedSeparatingOrbit_normalForm_entry_control graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative orbit normalized compatible
  have targetLimit : Tendsto (fun time => coordinate (orbitUnstableShape orbit time)) atBot (𝓝 0) := by
    have actual := coordinateSmooth.continuousAt.tendsto.comp
      (continuous_fst.continuousAt.tendsto.comp
        (normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized))
    simpa only [coordinateZero] using actual
  have targetSmall := targetLimit.eventually (eventually_lt_nhds accuracyPositive)
  obtain ⟨incomingTime, entry, positive, small, graphIdentity⟩ :=
    (entry.and ((normalizedSeparatingOrbit_eventually_positive_coordinate coordinateZero
      coordinateDerivative orbit normalized).and (targetSmall.and compatible))).exists
  refine ⟨incomingTime, coordinate (orbitUnstableShape orbit incomingTime), positive,
    radius, radiusPositive, accuracy / constant, div_pos accuracyPositive (by linarith),
    rfl, small, graphIdentity, ?_⟩
  intro point pointSmall close
  apply (entry point pointSmall).trans_lt
  have bound := mul_lt_mul_of_pos_left close (by linarith : 0 < constant)
  simpa only [mul_div_cancel₀ accuracy (ne_of_gt (by linarith : 0 < constant))] using bound

end EulerNonuniqueness.Section6
