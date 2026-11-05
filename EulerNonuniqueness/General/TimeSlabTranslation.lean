import Mathlib

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem measurePreserving_timeSlab_translation {Domain : Type*} [MeasurableSpace Domain]
    (measure : Measure Domain) [SFinite measure] (shift length : ℝ) :
    MeasurePreserving (fun point : ℝ × Domain => (shift + point.1, point.2))
      ((volume.restrict (Ioo 0 length)).prod measure)
      ((volume.restrict (Ioo shift (shift + length))).prod measure) := by
  have preserving := (measurePreserving_add_left (volume : Measure ℝ) shift).restrict_preimage
    (measurableSet_Ioo : MeasurableSet (Ioo shift (shift + length)))
  have preimage : (fun time : ℝ => shift + time) ⁻¹' Ioo shift (shift + length) = Ioo 0 length := by
    ext time
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro inside <;> constructor <;> linarith [inside.1, inside.2]
  rw [preimage] at preserving
  exact preserving.prod (MeasurePreserving.id measure)

theorem measurableEmbedding_timeSlab_translation {Domain : Type*} [MeasurableSpace Domain]
    (shift : ℝ) : MeasurableEmbedding (fun point : ℝ × Domain => (shift + point.1, point.2)) :=
  (MeasurableEquiv.addLeft shift).measurableEmbedding.prodMap (MeasurableEmbedding.id)

end EulerNonuniqueness
