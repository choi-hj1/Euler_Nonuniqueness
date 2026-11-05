import EulerNonuniqueness.Section3.PhasedContourField
import EulerNonuniqueness.Section3.FiniteContourMaterial
import EulerNonuniqueness.Section3.SimilarityPatchBiotSavart

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance phasedContourMaterialRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.phasedPhysicalContour_tangent {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) (label : ℝ) :
    (configuration.phasedPhysicalContour phase data index).val.2.val.1 label =
      configuration.radius index • ((phase index : ℂ) * (data index).val.2.val.1 label) := by
  change 0 + configuration.radius index • ((phase index : ℂ) * (data index).val.2.val.1 label) = _
  exact zero_add _

theorem FiniteContourConfiguration.phasedVectorField_label_value {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf)
    (nearby : ∀ index, ‖data index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (bounded : ∀ index, ‖data index‖ ≤ 3) (index : Fin count) (label : ℝ) :
    (configuration.phasedVectorField phase data index).val.1 label =
      configuration.density index • contourVelocity (data index).val.1 (data index).val.2.val.1 label (-Real.pi) Real.pi +
      ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
        ((((phase index)⁻¹ : Circle) : ℂ) *
          pointContourVelocity (configuration.phasedPhysicalContour phase data other).val.1
            (configuration.phasedPhysicalContour phase data other).val.2.val.1
            ((configuration.phasedPhysicalContour phase data index).val.1 label) (-Real.pi) Real.pi) := by
  let evaluation := contourLabelEvaluation label
  change evaluation (configuration.phasedVectorField phase data index) = _
  unfold FiniteContourConfiguration.phasedVectorField
  rw [evaluation.map_add, evaluation.map_smul, map_sum]
  rw [extendedContourVelocity_eq (data index) (nearby index)]
  congr 1
  apply Finset.sum_congr rfl
  intro other member
  rw [evaluation.map_smul]
  change (configuration.density other / configuration.radius index) •
      ((((phase index)⁻¹ : Circle) : ℂ) *
        (extendedCrossContourVelocity (configuration.phasedPhysicalContour phase data index)
          (configuration.phasedPhysicalContour phase data other)).val.1 label) = _
  have distinct : index ≠ other := (Finset.ne_of_mem_erase member).symm
  rw [extendedCrossContourVelocity_eq _ _ (configuration.crossGap_pos index other distinct)
    (configuration.phasedPhysicalContour_separated phase data index other (bounded index) (bounded other))]
  rw [crossContourVelocityBanach_value]

theorem FiniteContourConfiguration.phased_physical_vectorField_label_value {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf)
    (nearby : ∀ index, ‖data index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (bounded : ∀ index, ‖data index‖ ≤ 3) (index : Fin count) (label : ℝ) :
    configuration.radius index • ((phase index : ℂ) * (configuration.phasedVectorField phase data index).val.1 label) =
      configuration.density index • pointContourVelocity (configuration.phasedPhysicalContour phase data index).val.1
        (configuration.phasedPhysicalContour phase data index).val.2.val.1
        ((configuration.phasedPhysicalContour phase data index).val.1 label) (-Real.pi) Real.pi +
      ∑ other ∈ Finset.univ.erase index, configuration.density other •
        pointContourVelocity (configuration.phasedPhysicalContour phase data other).val.1
          (configuration.phasedPhysicalContour phase data other).val.2.val.1
          ((configuration.phasedPhysicalContour phase data index).val.1 label) (-Real.pi) Real.pi := by
  have safe : ∀ index, ‖data index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    intro source
    exact lt_min ((nearby source).trans_le (min_le_left _ _) |>.trans (by norm_num))
      ((nearby source).trans_le (min_le_right _ _))
  have self_identity :
      pointContourVelocity (configuration.phasedPhysicalContour phase data index).val.1
        (configuration.phasedPhysicalContour phase data index).val.2.val.1
        ((configuration.phasedPhysicalContour phase data index).val.1 label) (-Real.pi) Real.pi =
      configuration.radius index • ((phase index : ℂ) *
        contourVelocity (data index).val.1 (data index).val.2.val.1 label (-Real.pi) Real.pi) := by
    have curveIdentity : (configuration.phasedPhysicalContour phase data index).val.1 =
        (fun source => configuration.center index + configuration.radius index • ((phase index : ℂ) * (data index).val.1 source)) := rfl
    have tangentIdentity : (configuration.phasedPhysicalContour phase data index).val.2.val.1 =
        (fun source => configuration.radius index • ((phase index : ℂ) * (data index).val.2.val.1 source)) := by
      funext source
      exact configuration.phasedPhysicalContour_tangent phase data index source
    rw [curveIdentity, tangentIdentity]
    exact similarityContour_self_velocity _ (configuration.radius_pos index) _ _
      ((nearby index).trans_le (min_le_left _ _)) ((nearby index).trans_le (min_le_right _ _)) label
  rw [configuration.phasedVectorField_label_value phase data safe bounded index label,
    self_identity]
  simp only [Complex.real_smul, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro other member
    rw [Circle.coe_inv]
    push_cast
    field_simp [(configuration.radius_pos index).ne', Circle.coe_ne_zero (phase index)]
    <;> ring

end EulerNonuniqueness.Paper
