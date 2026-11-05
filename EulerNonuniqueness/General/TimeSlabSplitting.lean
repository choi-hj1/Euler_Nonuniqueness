import Mathlib

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem timeSlabMeasure_split {Domain : Type*} [MeasurableSpace Domain]
    (measure : Measure Domain) [SFinite measure] {first second : ℝ}
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    (volume.restrict (Ioo 0 (first + second))).prod measure =
      (volume.restrict (Ioo 0 first)).prod measure +
        (volume.restrict (Ioo first (first + second))).prod measure := by
  have timeSplit : (volume : Measure ℝ).restrict (Ioo 0 (first + second)) =
      volume.restrict (Ioo 0 first) + volume.restrict (Ioo first (first + second)) := by
    simp only [restrict_Ioo_eq_restrict_Ioc]
    rw [← Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc firstNonnegative (by linarith)]
  rw [timeSplit, Measure.add_prod]

end EulerNonuniqueness
