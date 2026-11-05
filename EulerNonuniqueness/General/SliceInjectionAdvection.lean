import EulerNonuniqueness.General.InjectionAdvection

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem measurable_slice_injectionAdvection {Parameter Space : Type*}
    [MeasurableSpace Parameter] [MeasurableSpace Space]
    [StandardBorelSpace Parameter] [StandardBorelSpace Space]
    [MeasurableSpace.CountablySeparated Parameter] [MeasurableSpace.CountablySeparated Space]
    {flow : Parameter → Space → Space}
    (measurable : Measurable (Function.uncurry flow))
    (injective : ∀ parameter, Function.Injective (flow parameter))
    {density : Space → ℝ} (densityMeasurable : Measurable density) :
    Measurable (fun point : Parameter × Space => injectionAdvection (flow point.1) density point.2) := by
  let spacetimeMap := fun point : Parameter × Space => (point.1, flow point.1 point.2)
  have mapMeasurable : Measurable spacetimeMap := measurable_fst.prodMk measurable
  have mapInjective : Function.Injective spacetimeMap := by
    rintro ⟨firstParameter, firstPosition⟩ ⟨secondParameter, secondPosition⟩ equal
    have parameters : firstParameter = secondParameter := congrArg Prod.fst equal
    subst secondParameter
    have positions := injective firstParameter (congrArg Prod.snd equal)
    exact Prod.ext rfl positions
  have embedding := mapMeasurable.measurableEmbedding mapInjective
  have jointMeasurable : Measurable (injectionAdvection spacetimeMap (fun point => density point.2)) :=
    embedding.measurable_extend (densityMeasurable.comp measurable_snd) measurable_const
  convert jointMeasurable using 1
  ext point
  obtain ⟨parameter, position⟩ := point
  by_cases inside : position ∈ range (flow parameter)
  · obtain ⟨preimage, rfl⟩ := inside
    rw [injectionAdvection_apply (injective parameter)]
    exact (injectionAdvection_apply mapInjective (fun point => density point.2) (parameter, preimage)).symm
  · have spacetimeOutside : (parameter, position) ∉ range spacetimeMap := by
      rintro ⟨⟨otherParameter, otherPosition⟩, equal⟩
      have parameters : otherParameter = parameter := congrArg Prod.fst equal
      subst otherParameter
      exact inside ⟨otherPosition, congrArg Prod.snd equal⟩
    rw [injectionAdvection_eq_zero_of_not_mem_range density inside,
      injectionAdvection_eq_zero_of_not_mem_range (fun point => density point.2) spacetimeOutside]

end EulerNonuniqueness
