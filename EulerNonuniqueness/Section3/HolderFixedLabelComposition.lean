import EulerNonuniqueness.Section3.HolderLabelComposition

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance fixedLabelHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph

namespace PeriodicC1LabelMap

def composeHolder (labels : PeriodicC1LabelMap) (data : PeriodicHolderHalf) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction (fun label => data.val.1 (labels.map label))
    (data.val.1.continuous.comp labels.continuous) ‖data‖ (‖data‖ * Real.sqrt labels.bound)
    (fun label => PeriodicHolderHalf.value_bound data _)
    (fun first second => by
      apply (PeriodicHolderHalf.holder_bound data _ _).trans
      have root := Real.sqrt_le_sqrt (labels.lipschitz_bound first second)
      rw [Real.sqrt_mul labels.bound_nonnegative] at root
      exact (mul_le_mul_of_nonneg_left root (norm_nonneg data)).trans_eq (by ring))
    (fun label => by
      change data.val.1 (labels.map (label + 2 * Real.pi)) = data.val.1 (labels.map label)
      rw [labels.add_period, PeriodicHolderHalf.periodic data])

theorem composeHolder_value (labels : PeriodicC1LabelMap) (data : PeriodicHolderHalf) (label : ℝ) :
    (labels.composeHolder data).val.1 label = data.val.1 (labels.map label) := rfl

theorem composeHolder_norm_bound (labels : PeriodicC1LabelMap) (data : PeriodicHolderHalf) :
    ‖labels.composeHolder data‖ ≤ (1 + Real.sqrt labels.bound) * ‖data‖ := by
  have bound : ‖labels.composeHolder data‖ ≤ max ‖data‖ (‖data‖ * Real.sqrt labels.bound) := by
    unfold composeHolder
    exact PeriodicHolderHalf.ofFunction_norm_bound _ _ (norm_nonneg data)
      (mul_nonneg (norm_nonneg data) (Real.sqrt_nonneg _)) _ _ _
  apply bound.trans
  apply max_le <;> nlinarith [norm_nonneg data, Real.sqrt_nonneg labels.bound]

def composeHolderCLM (labels : PeriodicC1LabelMap) : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  LinearMap.mkContinuous
    { toFun := labels.composeHolder
      map_add' := fun first second => by
        apply PeriodicHolderHalf.ext_value
        intro label
        rfl
      map_smul' := fun scalar data => by
        apply PeriodicHolderHalf.ext_value
        intro label
        rfl }
    (1 + Real.sqrt labels.bound) labels.composeHolder_norm_bound

theorem composeHolderCLM_value (labels : PeriodicC1LabelMap) (data : PeriodicHolderHalf) (label : ℝ) :
    (labels.composeHolderCLM data).val.1 label = data.val.1 (labels.map label) := rfl

end PeriodicC1LabelMap

end EulerNonuniqueness.Paper
