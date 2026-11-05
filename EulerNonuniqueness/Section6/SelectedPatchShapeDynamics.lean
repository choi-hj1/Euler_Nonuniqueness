import EulerNonuniqueness.Section6.ActualExternalCentroidDynamics
import EulerNonuniqueness.Section6.PatchPointFieldIdentity
import EulerNonuniqueness.Section6.CoherentPointShapeChart

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem fourPointShapeChart_actual_forced_equation {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart (trajectory time)).1
      (fourPointOddPart (trajectory time)).2))
    (normOrder : ‖(fourPointOddPart (trajectory time)).2‖ < ‖(fourPointOddPart (trajectory time)).1‖)
    (left : (((fourPointOddPart (trajectory time)).2 / (fourPointOddPart (trajectory time)).1) ^ 2).re < 0)
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fun current => pointShapeChart
        (fourPointOddPart (trajectory current)).1 (fourPointOddPart (trajectory current)).2)
      (shapeChartVelocity
          (coefficient / (‖(fourPointOddPart (trajectory time)).1‖ ^ 2 -
            ‖(fourPointOddPart (trajectory time)).2‖ ^ 2))
          (pointShapeChart (fourPointOddPart (trajectory time)).1 (fourPointOddPart (trajectory time)).2) +
        pointShapeForcing (fourPointOddPart (trajectory time)).1 (fourPointOddPart (trajectory time)).2
          (fourPointTotalOddForcing coefficient (trajectory time) forcing).1
          (fourPointTotalOddForcing coefficient (trajectory time) forcing).2) time := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  have squareNonzero : star (fourPointOddPart (trajectory time)).1 ^ 2 -
      star (fourPointOddPart (trajectory time)).2 ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have derivative := fourPointOddPart_actual_forced_equation equation
  exact pointShapeChart_forced_equation coefficient
    (positive := fun current => (fourPointOddPart (trajectory current)).1)
    (negative := fun current => (fourPointOddPart (trajectory current)).2)
    (positiveForcing := (fourPointTotalOddForcing coefficient (trajectory time) forcing).1)
    (negativeForcing := (fourPointTotalOddForcing coefficient (trajectory time) forcing).2)
    positiveNonzero negativeNonzero squareNonzero normOrder left
    (by simpa only [Prod.fst_add, fourPointTotalOddForcing] using derivative.fst)
    (by simpa only [Prod.snd_add, fourPointTotalOddForcing] using derivative.snd)

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem selectedInternalPointField_fourPointField (flow : FiniteLiteralPatchFlow configuration)
    (labels : Fin 4 → Fin count) (injective : Function.Injective labels) (coefficient time : ℝ)
    (coefficientEquation : ∀ target : Fin 4,
      configuration.density (labels target) * (Real.pi * configuration.radius (labels target) ^ 2) /
        (2 * Real.pi) = coefficient * Section6.fourPointSign target)
    (target : Fin 4) :
    flow.subfamilyInternalPointField (Finset.univ.image labels) time (labels target) =
      Section6.fourPointField coefficient (fun source => flow.centroid time (labels source)) target := by
  unfold subfamilyInternalPointField
  rw [← Finset.image_erase injective Finset.univ target]
  rw [Finset.sum_image (fun first _ second _ equality => injective equality)]
  rw [← Section6.finitePointField_eq_circulation_kernel_sum
    (fun source => configuration.density (labels source) * (Real.pi * configuration.radius (labels source) ^ 2))
    (fun source => flow.centroid time (labels source)) target]
  have coefficientsIdentity :
      (fun source : Fin 4 => configuration.density (labels source) *
        (Real.pi * configuration.radius (labels source) ^ 2) / (2 * Real.pi)) =
      (fun source : Fin 4 => coefficient * Section6.fourPointSign source) := funext coefficientEquation
  rw [coefficientsIdentity, Section6.finitePointField_fourPoint_identity]

theorem selected_centroid_actual_external_equation (flow : FiniteLiteralPatchFlow configuration)
    (labels : Fin 4 → Fin count) (injective : Function.Injective labels) (coefficient : ℝ)
    (coefficientEquation : ∀ target : Fin 4,
      configuration.density (labels target) * (Real.pi * configuration.radius (labels target) ^ 2) /
        (2 * Real.pi) = coefficient * Section6.fourPointSign target)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (target : Fin 4) :
    HasDerivAt (fun current => flow.centroid current (labels target))
      (Section6.fourPointField coefficient (fun source => flow.centroid time (labels source)) target +
        (flow.subfamilyExternalPatchField (Finset.univ.image labels) time (flow.centroid time (labels target)) +
          flow.subfamilyInternalDeformationResidual (Finset.univ.image labels) time (labels target) +
          flow.subfamilyExternalReceiverResidual (Finset.univ.image labels) time (labels target))) time := by
  have actual := flow.centroid_actual_external_patch_equation (Finset.univ.image labels) inside (labels target)
    (Finset.mem_image.mpr ⟨target, Finset.mem_univ target, rfl⟩)
  rw [flow.selectedInternalPointField_fourPointField labels injective coefficient time coefficientEquation target] at actual
  simpa only [add_assoc] using actual

theorem selected_centroid_coherent_shape_equation (flow : FiniteLiteralPatchFlow configuration)
    (labels : Fin 4 → Fin count) (injective : Function.Injective labels) (coefficient : ℝ)
    (coefficientEquation : ∀ target : Fin 4,
      configuration.density (labels target) * (Real.pi * configuration.radius (labels target) ^ 2) /
        (2 * Real.pi) = coefficient * Section6.fourPointSign target)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) :
    let trajectory := fun (current : ℝ) (target : Fin 4) => flow.centroid current (labels target)
    let positions := trajectory time
    let point := Section6.fourPointOddPart positions
    let forcing := fun target =>
      flow.subfamilyExternalPatchField (Finset.univ.image labels) time (positions target) +
        flow.subfamilyInternalDeformationResidual (Finset.univ.image labels) time (labels target) +
        flow.subfamilyExternalReceiverResidual (Finset.univ.image labels) time (labels target)
    Section6.FourPointNoncollision (Section6.centrallySymmetricFourPoint point.1 point.2) →
    ‖point.2‖ < ‖point.1‖ → ((point.2 / point.1) ^ 2).re < 0 →
    HasDerivAt (fun current => Section6.pointShapeChart
        (Section6.fourPointOddPart (trajectory current)).1 (Section6.fourPointOddPart (trajectory current)).2)
      (Section6.shapeChartVelocity (coefficient / (‖point.1‖ ^ 2 - ‖point.2‖ ^ 2))
          (Section6.pointShapeChart point.1 point.2) +
        Section6.pointShapeForcing point.1 point.2
          (Section6.fourPointTotalOddForcing coefficient positions forcing).1
          (Section6.fourPointTotalOddForcing coefficient positions forcing).2) time := by
  dsimp only
  intro noncollision normOrder left
  exact Section6.fourPointShapeChart_actual_forced_equation
    (trajectory := fun (current : ℝ) (target : Fin 4) => flow.centroid current (labels target))
    (coefficient := coefficient)
    (forcing := fun target => flow.subfamilyExternalPatchField (Finset.univ.image labels) time
      (flow.centroid time (labels target)) +
        flow.subfamilyInternalDeformationResidual (Finset.univ.image labels) time (labels target) +
        flow.subfamilyExternalReceiverResidual (Finset.univ.image labels) time (labels target))
    noncollision normOrder left (flow.selected_centroid_actual_external_equation labels injective coefficient coefficientEquation inside)

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
