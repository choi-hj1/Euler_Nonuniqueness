import EulerNonuniqueness.Section8.Globalization
import Mathlib.Topology.Order.ProjIcc

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem aestronglyMeasurable_spacetime_of_measurable_Icc
    {Value : Type*} [NormedAddCommGroup Value] [MeasurableSpace Value] [BorelSpace Value]
    [SecondCountableTopology Value] {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    {field : ℝ × Plane → Value}
    (measurable : Measurable (fun point : Icc (0 : ℝ) horizon × Plane => field (point.1, point.2))) :
    AEStronglyMeasurable field (spacetimeMeasure horizon) := by
  have extensionMeasurable : Measurable (fun point : ℝ × Plane =>
      field (projIcc 0 horizon nonnegative point.1, point.2)) :=
    measurable.comp (((continuous_projIcc : Continuous (projIcc 0 horizon nonnegative)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  apply extensionMeasurable.aestronglyMeasurable.congr
  have timeInside : ∀ᵐ point ∂spacetimeMeasure horizon, point.1 ∈ Ioo 0 horizon :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [timeInside] with point inside
  rw [projIcc_of_mem (h := nonnegative) ⟨inside.1.le, inside.2.le⟩]

theorem integrable_spacetime_of_supported_bounded
    {Value : Type*} [NormedAddCommGroup Value] {horizon radius bound : ℝ}
    {field : ℝ × Plane → Value} (measurable : AEStronglyMeasurable field (spacetimeMeasure horizon))
    (bounded : ∀ time ∈ Ioo 0 horizon, ∀ position ∈ Metric.closedBall (0 : Plane) radius, ‖field (time, position)‖ ≤ bound)
    (supported : ∀ time ∈ Ioo 0 horizon, ∀ position, position ∉ Metric.closedBall (0 : Plane) radius → field (time, position) = 0) :
    Integrable field (spacetimeMeasure horizon) := by
  have spatialIntegrable : Integrable ((Metric.closedBall (0 : Plane) radius).indicator (fun _ => bound)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) radius).measure_lt_top))
  have temporalIntegrable : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo 0 horizon)) := integrable_const _
  have dominator : Integrable (fun point : ℝ × Plane =>
      (Metric.closedBall (0 : Plane) radius).indicator (fun _ => bound) point.2) (spacetimeMeasure horizon) := by
    simpa only [one_mul] using temporalIntegrable.mul_prod spatialIntegrable
  apply dominator.mono' measurable
  have timeInside : ∀ᵐ point ∂spacetimeMeasure horizon, point.1 ∈ Ioo 0 horizon :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [timeInside] with point inside
  by_cases positionInside : point.2 ∈ Metric.closedBall (0 : Plane) radius
  · simpa only [indicator_of_mem positionInside] using bounded point.1 inside point.2 positionInside
  · simp only [indicator_of_not_mem positionInside, supported point.1 inside point.2 positionInside, norm_zero, le_refl]

end EulerNonuniqueness
