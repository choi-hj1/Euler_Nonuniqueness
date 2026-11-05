import Mathlib

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace MeasureTheory

theorem norm_setIntegral_sub_le_measure_symmDiff_mul
    {domain value : Type*} [MeasureSpace domain]
    [NormedAddCommGroup value] [NormedSpace ℝ value] [CompleteSpace value]
    {first second : Set domain} (firstMeasurable : MeasurableSet first) (secondMeasurable : MeasurableSet second)
    (finite : volume (first ∆ second) < ⊤) {function : domain → value}
    (firstIntegrable : IntegrableOn function first) (secondIntegrable : IntegrableOn function second)
    {bound : ℝ} (bounded : ∀ position ∈ first ∆ second, ‖function position‖ ≤ bound) :
    ‖(∫ position in first, function position) - (∫ position in second, function position)‖ ≤
      volume.real (first ∆ second) * bound := by
  have firstIndicator := (integrable_indicator_iff firstMeasurable).mpr firstIntegrable
  have secondIndicator := (integrable_indicator_iff secondMeasurable).mpr secondIntegrable
  have majorant : Integrable ((first ∆ second).indicator (fun _ : domain => bound)) :=
    (integrable_indicator_iff (firstMeasurable.symmDiff secondMeasurable)).mpr
      (integrableOn_const.mpr (Or.inr finite))
  have estimate := norm_integral_le_of_norm_le
    (f := fun position => first.indicator function position - second.indicator function position)
    majorant (by
      filter_upwards [] with position
      by_cases inFirst : position ∈ first <;> by_cases inSecond : position ∈ second
      · simp [inFirst, inSecond, Set.mem_symmDiff]
      · have bound := bounded position (Set.mem_symmDiff.mpr (Or.inl ⟨inFirst, inSecond⟩))
        simpa [inFirst, inSecond, Set.mem_symmDiff] using bound
      · have bound := bounded position (Set.mem_symmDiff.mpr (Or.inr ⟨inSecond, inFirst⟩))
        simpa [inFirst, inSecond, Set.mem_symmDiff] using bound
      · simp [inFirst, inSecond, Set.mem_symmDiff])
  rw [integral_sub (f := first.indicator function) (g := second.indicator function)
    firstIndicator secondIndicator, integral_indicator firstMeasurable, integral_indicator secondMeasurable,
    integral_indicator (firstMeasurable.symmDiff secondMeasurable), integral_const] at estimate
  simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] using estimate

end MeasureTheory
