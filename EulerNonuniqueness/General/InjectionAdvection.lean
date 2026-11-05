import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace EulerNonuniqueness

def injectionAdvection {Source Target : Type*} (map : Source → Target) (density : Source → ℝ) : Target → ℝ :=
  Function.extend map density 0

theorem injectionAdvection_apply {Source Target : Type*} {map : Source → Target}
    (injective : Function.Injective map) (density : Source → ℝ) (point : Source) :
    injectionAdvection map density (map point) = density point :=
  injective.extend_apply density 0 point

theorem injectionAdvection_eq_zero_of_not_mem_range {Source Target : Type*}
    {map : Source → Target} (density : Source → ℝ) {point : Target} (outside : point ∉ range map) :
    injectionAdvection map density point = 0 :=
  Function.extend_apply' (f := map) density (0 : Target → ℝ) point outside

theorem indicator_range_injectionAdvection {Source Target : Type*}
    (map : Source → Target) (density : Source → ℝ) :
    (range map).indicator (injectionAdvection map density) = injectionAdvection map density := by
  ext point
  by_cases inside : point ∈ range map
  · exact indicator_of_mem inside _
  · rw [indicator_of_not_mem inside, injectionAdvection_eq_zero_of_not_mem_range density inside]

theorem support_injectionAdvection {Source Target : Type*} {map : Source → Target}
    (injective : Function.Injective map) (density : Source → ℝ) :
    support (injectionAdvection map density) = map '' support density := by
  ext point
  constructor
  · intro nonzero
    by_cases inside : point ∈ range map
    · obtain ⟨preimage, rfl⟩ := inside
      exact ⟨preimage, by simpa only [mem_support, injectionAdvection_apply injective] using nonzero, rfl⟩
    · exact False.elim (nonzero (injectionAdvection_eq_zero_of_not_mem_range density inside))
  · rintro ⟨preimage, nonzero, rfl⟩
    simpa only [mem_support, injectionAdvection_apply injective] using nonzero

theorem eLpNorm_injectionAdvection {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target]
    {map : Source → Target} (embedding : MeasurableEmbedding map)
    {sourceMeasure : Measure Source} {targetMeasure : Measure Target}
    (pushforward : Measure.map map sourceMeasure = targetMeasure.restrict (range map))
    (density : Source → ℝ) (exponent : ℝ≥0∞) :
    eLpNorm (injectionAdvection map density) exponent targetMeasure = eLpNorm density exponent sourceMeasure := by
  calc
    _ = eLpNorm ((range map).indicator (injectionAdvection map density)) exponent targetMeasure := by
      rw [indicator_range_injectionAdvection]
    _ = eLpNorm (injectionAdvection map density) exponent (targetMeasure.restrict (range map)) :=
      eLpNorm_indicator_eq_eLpNorm_restrict embedding.measurableSet_range
    _ = eLpNorm (injectionAdvection map density) exponent (Measure.map map sourceMeasure) := by rw [pushforward]
    _ = eLpNorm ((injectionAdvection map density) ∘ map) exponent sourceMeasure := embedding.eLpNorm_map_measure
    _ = _ := by rw [show injectionAdvection map density ∘ map = density from Function.extend_comp embedding.injective density 0]

theorem memLp_injectionAdvection {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target]
    {map : Source → Target} (embedding : MeasurableEmbedding map)
    {sourceMeasure : Measure Source} {targetMeasure : Measure Target}
    (pushforward : Measure.map map sourceMeasure = targetMeasure.restrict (range map))
    {density : Source → ℝ} {exponent : ℝ≥0∞} (member : MemLp density exponent sourceMeasure) :
    MemLp (injectionAdvection map density) exponent targetMeasure := by
  have restricted : MemLp (injectionAdvection map density) exponent (targetMeasure.restrict (range map)) := by
    rw [← pushforward, embedding.memLp_map_measure_iff]
    simpa only [injectionAdvection, Function.extend_comp embedding.injective] using member
  have global := (memLp_indicator_iff_restrict embedding.measurableSet_range).mpr restricted
  rwa [indicator_range_injectionAdvection] at global

theorem integral_injectionAdvection_smul {Source Target Value : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {map : Source → Target} (embedding : MeasurableEmbedding map)
    {sourceMeasure : Measure Source} {targetMeasure : Measure Target}
    (pushforward : Measure.map map sourceMeasure = targetMeasure.restrict (range map))
    (density : Source → ℝ) (coefficient : Target → Value) :
    (∫ point, injectionAdvection map density point • coefficient point ∂targetMeasure) =
      ∫ point, density point • coefficient (map point) ∂sourceMeasure := by
  have indicatorEquality : (range map).indicator
      (fun point => injectionAdvection map density point • coefficient point) =
        (fun point => injectionAdvection map density point • coefficient point) := by
    ext point
    by_cases inside : point ∈ range map
    · exact indicator_of_mem inside _
    · rw [indicator_of_not_mem inside, injectionAdvection_eq_zero_of_not_mem_range density inside, zero_smul]
  rw [← indicatorEquality, integral_indicator embedding.measurableSet_range, ← pushforward, embedding.integral_map]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    simp only [injectionAdvection_apply embedding.injective]

end EulerNonuniqueness
