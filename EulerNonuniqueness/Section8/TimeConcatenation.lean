import EulerNonuniqueness.Section8.TerminalTransportTrace
import EulerNonuniqueness.Section8.TimeShiftTest
import EulerNonuniqueness.General.TimeSlabTranslation
import EulerNonuniqueness.General.TimeSlabSplitting

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace EulerNonuniqueness

def timeConcatenation {Value : Type*} (join : ℝ) (earlier later : ℝ → Value) (time : ℝ) : Value :=
  if time ≤ join then earlier time else later (time - join)

theorem WeakTransportOn.timeConcatenation
    {first second : ℝ} {initial terminal : Vorticity}
    {earlier later : Evolution} {earlierVelocity laterVelocity : ℝ → Velocity}
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (earlierTransport : WeakTransportOn first initial earlier earlierVelocity)
    (laterTransport : WeakTransportOn second terminal later laterVelocity)
    (trace : earlier first =ᵐ[volume] terminal)
    (integrable : ∀ test : ℝ × Plane → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      Integrable (fun point : ℝ × Plane => earlier point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (earlierVelocity point.1 point.2)))
          (spacetimeMeasure first))
    (continuous : ∀ test : ℝ × Plane → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      ContinuousOn (fun time => ∫ position, earlier time position * test (time, position)) (Icc 0 first)) :
    WeakTransportOn (first + second) initial (EulerNonuniqueness.timeConcatenation first earlier later)
      (EulerNonuniqueness.timeConcatenation first earlierVelocity laterVelocity) := by
  intro test admissible
  let main := fun point : ℝ × Plane => EulerNonuniqueness.timeConcatenation first earlier later point.1 point.2 *
    (timeDerivative test point + spatialDerivative test point
      (EulerNonuniqueness.timeConcatenation first earlierVelocity laterVelocity point.1 point.2))
  let before := fun point : ℝ × Plane => earlier point.1 point.2 *
    (timeDerivative test point + spatialDerivative test point (earlierVelocity point.1 point.2))
  let after := fun point : ℝ × Plane => later point.1 point.2 *
    (timeDerivative (timeShiftTest first test) point +
      spatialDerivative (timeShiftTest first test) point (laterVelocity point.1 point.2))
  let laterMeasure := (volume.restrict (Ioo first (first + second))).prod (volume : Measure Plane)
  have beforeEqual : main =ᵐ[spacetimeMeasure first] before := by
    have timeInside : ∀ᵐ point : ℝ × Plane ∂spacetimeMeasure first, point.1 ∈ Ioo 0 first :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [timeInside] with point inside
    simp only [main, before, EulerNonuniqueness.timeConcatenation, if_pos inside.2.le]
  have afterEqual : (fun point : ℝ × Plane => main (first + point.1, point.2)) =ᵐ[spacetimeMeasure second] after := by
    have timeInside : ∀ᵐ point : ℝ × Plane ∂spacetimeMeasure second, point.1 ∈ Ioo 0 second :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [timeInside] with point inside
    have outside : ¬ first + point.1 ≤ first := by linarith [inside.1]
    simp only [main, after, EulerNonuniqueness.timeConcatenation, if_neg outside,
      add_sub_cancel_left, timeDerivative_timeShiftTest admissible.1,
      spatialDerivative_timeShiftTest admissible.1]
  have firstIntegrable : Integrable main (spacetimeMeasure first) :=
    (integrable test admissible.1 admissible.2.1).congr beforeEqual.symm
  have laterIdentity := laterTransport (timeShiftTest first test) (scalarTestOn_timeShiftTest admissible)
  have pulledIntegrable : Integrable (fun point : ℝ × Plane => main (first + point.1, point.2))
      (spacetimeMeasure second) := laterIdentity.1.congr afterEqual.symm
  have preserving := measurePreserving_timeSlab_translation (volume : Measure Plane) first second
  have embedding := measurableEmbedding_timeSlab_translation (Domain := Plane) first
  have secondIntegrable : Integrable main laterMeasure :=
    (preserving.integrable_comp_emb embedding).mp pulledIntegrable
  have measureSplit : spacetimeMeasure (first + second) = spacetimeMeasure first + laterMeasure :=
    timeSlabMeasure_split volume firstPositive.le secondPositive.le
  have wholeIntegrable : Integrable main (spacetimeMeasure (first + second)) := by
    rw [measureSplit]
    exact firstIntegrable.add_measure secondIntegrable
  have firstIntegral : (∫ point, main point ∂spacetimeMeasure first) =
      ∫ point, before point ∂spacetimeMeasure first := integral_congr_ae beforeEqual
  have secondIntegral : (∫ point, main point ∂laterMeasure) =
      ∫ point, after point ∂spacetimeMeasure second := by
    rw [← preserving.integral_comp embedding main]
    exact integral_congr_ae afterEqual
  have terminalIdentity := earlierTransport.terminal_test_identity firstPositive admissible.1 admissible.2.1
    (integrable test admissible.1 admissible.2.1) (continuous test admissible.1 admissible.2.1)
  have terminalIntegral : (∫ position, earlier first position * test (first, position)) =
      ∫ position, terminal position * timeShiftTest first test (0, position) := by
    apply integral_congr_ae
    filter_upwards [trace] with position equal
    simp [equal, timeShiftTest]
  refine ⟨wholeIntegrable, terminalIdentity.1, ?_⟩
  change (∫ point, main point ∂spacetimeMeasure (first + second)) + _ = 0
  rw [measureSplit, integral_add_measure firstIntegrable secondIntegrable, firstIntegral, secondIntegral]
  have beforeIdentity := terminalIdentity.2
  rw [terminalIntegral] at beforeIdentity
  have afterIdentity := laterIdentity.2.2
  change (∫ point, before point ∂spacetimeMeasure first) + _ = _ at beforeIdentity
  change (∫ point, after point ∂spacetimeMeasure second) + _ = 0 at afterIdentity
  linarith

end EulerNonuniqueness
