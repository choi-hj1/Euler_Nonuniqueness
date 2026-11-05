import EulerNonuniqueness.Section3.FiniteContourLocalEvolution
import EulerNonuniqueness.Section3.AffineContourSelfVelocity

open Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

set_option maxHeartbeats 1000000 in
theorem FiniteContourConfiguration.vectorField_label_value {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (nearby : ∀ index, ‖data index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (bounded : ∀ index, ‖data index‖ ≤ 3) (index : Fin count) (label : ℝ) :
    (configuration.vectorField data index).val.1 label =
      configuration.density index • contourVelocity (data index).val.1 (data index).val.2.val.1 label (-Real.pi) Real.pi +
      ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
        pointContourVelocity (configuration.physicalContour data other).val.1
          (configuration.physicalContour data other).val.2.val.1
          ((configuration.physicalContour data index).val.1 label) (-Real.pi) Real.pi := by
  let evaluation := contourLabelEvaluation label
  change evaluation (configuration.vectorField data index) = _
  unfold FiniteContourConfiguration.vectorField
  rw [evaluation.map_add, evaluation.map_smul, map_sum]
  rw [extendedContourVelocity_eq (data index) (nearby index)]
  congr 1
  apply Finset.sum_congr rfl
  intro other other_mem
  rw [evaluation.map_smul]
  have distinct : index ≠ other := (Finset.ne_of_mem_erase other_mem).symm
  rw [extendedCrossContourVelocity_eq _ _ (configuration.crossGap_pos index other distinct)
    (configuration.physicalContour_separated data index other (bounded index) (bounded other))]
  congr 1
  exact crossContourVelocityBanach_value _ _ _ _ label

set_option maxHeartbeats 1000000 in
theorem FiniteContourConfiguration.physical_vectorField_label_value {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (nearby : ∀ index, ‖data index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (bounded : ∀ index, ‖data index‖ ≤ 3) (index : Fin count) (label : ℝ) :
    configuration.radius index • (configuration.vectorField data index).val.1 label =
      configuration.density index • pointContourVelocity (configuration.physicalContour data index).val.1
        (configuration.physicalContour data index).val.2.val.1
        ((configuration.physicalContour data index).val.1 label) (-Real.pi) Real.pi +
      ∑ other ∈ Finset.univ.erase index, configuration.density other •
        pointContourVelocity (configuration.physicalContour data other).val.1
          (configuration.physicalContour data other).val.2.val.1
          ((configuration.physicalContour data index).val.1 label) (-Real.pi) Real.pi := by
  rw [configuration.vectorField_label_value data nearby bounded index label, smul_add, Finset.smul_sum]
  congr 1
  · rw [smul_comm]
    congr 1
    exact (c1AffineContour_self_velocity (configuration.center index) (configuration.radius_pos index)
      (data index) (nearby index) label).symm
  · apply Finset.sum_congr rfl
    intro other other_mem
    rw [smul_smul]
    congr 1
    exact mul_div_cancel₀ (configuration.density other) (configuration.radius_pos index).ne'

set_option maxHeartbeats 1000000 in
theorem finite_contour_physical_material_evolution {count : ℕ} (configuration : FiniteContourConfiguration count) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → Fin count → PeriodicC1HolderHalf,
      solution 0 = standardContours count ∧
      (∀ time index, ‖solution time index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) ∧
      ∀ time ∈ Ioo (-duration) duration, ∀ index label,
        HasDerivAt (fun time => (configuration.physicalContour (solution time) index).val.1 label)
          (configuration.density index • pointContourVelocity (configuration.physicalContour (solution time) index).val.1
            (configuration.physicalContour (solution time) index).val.2.val.1
            ((configuration.physicalContour (solution time) index).val.1 label) (-Real.pi) Real.pi +
          ∑ other ∈ Finset.univ.erase index, configuration.density other •
            pointContourVelocity (configuration.physicalContour (solution time) other).val.1
              (configuration.physicalContour (solution time) other).val.2.val.1
              ((configuration.physicalContour (solution time) index).val.1 label) (-Real.pi) Real.pi) time := by
  obtain ⟨duration, duration_pos, solution, initial_eq, nearby, bounded, equation⟩ :=
    finite_contour_local_label_evolution configuration
  refine ⟨duration, duration_pos, solution, initial_eq, nearby, ?_⟩
  intro time time_mem index label
  have derivative := (hasDerivAt_const time (configuration.center index)).add
    ((equation time time_mem index label).const_smul (configuration.radius index))
  rw [zero_add, configuration.physical_vectorField_label_value (solution time) (nearby time) (bounded time) index label] at derivative
  exact derivative

end

end EulerNonuniqueness.Paper
