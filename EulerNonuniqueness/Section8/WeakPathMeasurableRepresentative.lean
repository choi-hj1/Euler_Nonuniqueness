import EulerNonuniqueness.General.SectionwiseMeasurableRepresentative
import EulerNonuniqueness.Section8.MollifiedTimeDerivative
import EulerNonuniqueness.Section8.WeakVorticityPathBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem exists_measurable_representative_of_weakL2_continuous
    {Time : Type*} [TopologicalSpace Time] [MeasurableSpace Time] [BorelSpace Time]
    {fields : Time → Vorticity}
    (integrable : ∀ time, Integrable (fields time))
    (weakContinuous : ∀ test : Vorticity, MemLp test 2 volume →
      Continuous (fun time => ∫ position, fields time position * test position)) :
    ∃ representative : Time → Vorticity,
      Measurable (Function.uncurry representative) ∧
        ∀ time, representative time =ᵐ[volume] fields time := by
  have timeContinuous (index : ℕ) (position : Plane) :
      Continuous (fun time => mollification (fields time) index position) := by
    have smooth : ContDiff ℝ ∞
        (fun source => (mollifierBump index).normed volume (position - source)) :=
      (mollifierBump index).contDiff_normed.comp (contDiff_const.sub contDiff_id)
    have compact : HasCompactSupport
        (fun source => (mollifierBump index).normed volume (position - source)) :=
      (mollifierBump index).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft position)
    convert weakContinuous _ (smooth.continuous.memLp_of_hasCompactSupport compact) using 1
    funext time
    exact mollification_eq_source_moment (fields time) index position
  apply exists_measurable_sectionwise_ae_eq_of_measurable_approximation
    (approximation := fun index point => mollification (fields point.1) index point.2)
  · intro index
    exact (measurable_uncurry_of_continuous_of_measurable
      (fun time => (contDiff_mollification (integrable time) index).continuous)
      (fun position => (timeContinuous index position).measurable)).comp measurable_swap
  · exact fun time => ae_tendsto_mollification (integrable time)

theorem exists_supported_measurable_representative_of_weakL2_continuous
    {Time : Type*} [TopologicalSpace Time] [MeasurableSpace Time] [BorelSpace Time]
    {fields : Time → Vorticity}
    (integrable : ∀ time, Integrable (fields time))
    (weakContinuous : ∀ test : Vorticity, MemLp test 2 volume →
      Continuous (fun time => ∫ position, fields time position * test position))
    {region : Set Plane} (regionMeasurable : MeasurableSet region)
    (supported : ∀ time, fields time =ᵐ[volume] region.indicator (fields time)) :
    ∃ representative : Time → Vorticity,
      Measurable (Function.uncurry representative) ∧
        (∀ time, representative time =ᵐ[volume] fields time) ∧
          ∀ time, Function.support (representative time) ⊆ region := by
  obtain ⟨raw, rawMeasurable, equal⟩ :=
    exists_measurable_representative_of_weakL2_continuous integrable weakContinuous
  let representative : Time → Vorticity := fun time => region.indicator (raw time)
  refine ⟨representative, ?_, ?_, fun time => support_indicator_subset⟩
  · exact Measurable.ite (regionMeasurable.preimage measurable_snd) rawMeasurable measurable_const
  · intro time
    filter_upwards [equal time, supported time] with position rawEqual supportEqual
    by_cases inside : position ∈ region
    · simpa only [representative, indicator_of_mem inside] using rawEqual
    · simpa only [representative, indicator_of_not_mem inside] using supportEqual.symm

end EulerNonuniqueness
