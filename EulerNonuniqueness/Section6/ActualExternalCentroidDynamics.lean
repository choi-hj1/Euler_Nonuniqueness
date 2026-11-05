import EulerNonuniqueness.Section6.ActualExternalReceiverError
import EulerNonuniqueness.Section6.FinitePatchSubfamily

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def subfamilyExternalPatchField (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (position : ℂ) : ℂ :=
  ∑ source ∈ Finset.univ \ selected, biotSavart (flow.componentVorticity time source) position

def subfamilyInternalPointField (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (receiver : Fin count) : ℂ :=
  ∑ source ∈ selected.erase receiver,
    (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
      biotSavartKernel (flow.centroid time receiver - flow.centroid time source)

def subfamilyInternalDeformationResidual (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (receiver : Fin count) : ℂ :=
  ∑ source ∈ selected.erase receiver,
    ((Real.pi * configuration.radius receiver ^ 2)⁻¹ •
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
      (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
        biotSavartKernel (flow.centroid time receiver - flow.centroid time source))

def subfamilyExternalReceiverResidual (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (receiver : Fin count) : ℂ :=
  ∑ source ∈ Finset.univ \ selected,
    ((Real.pi * configuration.radius receiver ^ 2)⁻¹ •
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
      biotSavart (flow.componentVorticity time source) (flow.centroid time receiver))

theorem subfamilyExternalPatchField_eq_biotSavart (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (position : ℂ) :
    flow.subfamilyExternalPatchField selected time position =
      biotSavart (flow.subfamilyVorticity (Finset.univ \ selected) time) position := by
  unfold subfamilyExternalPatchField biotSavart subfamilyVorticity
  simp_rw [Finset.sum_smul]
  exact (integral_finset_sum _ (fun source _ => integrable_biotSavart_integrand_of_L1_L4
    (flow.componentVorticity_integrable time source) (flow.componentVorticity_memLp time source _) position)).symm

theorem centroid_actual_external_patch_equation (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (receiver : Fin count) (member : receiver ∈ selected) :
    HasDerivAt (fun parameter => flow.centroid parameter receiver)
      (flow.subfamilyInternalPointField selected time receiver +
        flow.subfamilyExternalPatchField selected time (flow.centroid time receiver) +
        flow.subfamilyInternalDeformationResidual selected time receiver +
        flow.subfamilyExternalReceiverResidual selected time receiver) time := by
  let average := fun source => (Real.pi * configuration.radius receiver ^ 2)⁻¹ •
    (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position)
  have internal : flow.subfamilyInternalPointField selected time receiver +
      flow.subfamilyInternalDeformationResidual selected time receiver =
      ∑ source ∈ selected.erase receiver, average source := by
    unfold subfamilyInternalPointField subfamilyInternalDeformationResidual
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro source _
    dsimp only [average]
    abel
  have external : flow.subfamilyExternalPatchField selected time (flow.centroid time receiver) +
      flow.subfamilyExternalReceiverResidual selected time receiver =
      ∑ source ∈ Finset.univ \ selected, average source := by
    unfold subfamilyExternalPatchField subfamilyExternalReceiverResidual
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro source _
    dsimp only [average]
    abel
  have erase := Finset.sum_erase_add selected average member
  have own : average receiver = 0 := by
    dsimp only [average]
    rw [flow.component_self_integral_zero, smul_zero]
  rw [own, add_zero] at erase
  have partition := Finset.sum_sdiff (f := average) (Finset.subset_univ selected)
  have identity : flow.subfamilyInternalPointField selected time receiver +
      flow.subfamilyExternalPatchField selected time (flow.centroid time receiver) +
      flow.subfamilyInternalDeformationResidual selected time receiver +
      flow.subfamilyExternalReceiverResidual selected time receiver = ∑ source, average source := by
    calc
      _ = (flow.subfamilyInternalPointField selected time receiver +
          flow.subfamilyInternalDeformationResidual selected time receiver) +
          (flow.subfamilyExternalPatchField selected time (flow.centroid time receiver) +
          flow.subfamilyExternalReceiverResidual selected time receiver) := by abel
      _ = _ := by rw [internal, external, erase, add_comm]; exact partition
  rw [identity]
  exact flow.centroid_hasDerivAt_sum_integrals inside receiver

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
