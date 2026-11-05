import EulerNonuniqueness.Section3.ContourLocalEvolution

open Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance contourEvaluationHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance contourEvaluationC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def contourTangentEvaluation (label : ℝ) : PeriodicC1HolderHalf →L[ℝ] ℂ := by
  let evaluation : PeriodicC1HolderHalf →ₗ[ℝ] ℂ := {
    toFun := fun data => data.val.2.val.1 label
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := ℂ)
    evaluation 1 (fun data => by
      change ‖data.val.2.val.1 label‖ ≤ 1 * ‖data‖
      simpa only [one_mul] using PeriodicC1HolderHalf.speed_bound data label)

theorem continuous_contour_value_joint {X : Type*} [TopologicalSpace X]
    (shape : X → PeriodicC1HolderHalf) (shape_continuous : Continuous shape) :
    Continuous (fun pair : X × ℝ => (shape pair.1).val.1 pair.2) := by
  have value_continuous : Continuous (fun parameter => (shape parameter).val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp shape_continuous)
  exact BoundedContinuousFunction.continuous_eval.comp
    ((value_continuous.comp continuous_fst).prodMk continuous_snd)

theorem continuous_contour_tangent_joint {X : Type*} [TopologicalSpace X]
    (shape : X → PeriodicC1HolderHalf) (shape_continuous : Continuous shape) :
    Continuous (fun pair : X × ℝ => (shape pair.1).val.2.val.1 pair.2) := by
  have holder_continuous : Continuous (fun parameter => (shape parameter).val.2) :=
    continuous_snd.comp (continuous_subtype_val.comp shape_continuous)
  have tangent_continuous : Continuous (fun parameter => (shape parameter).val.2.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp holder_continuous)
  exact BoundedContinuousFunction.continuous_eval.comp
    ((tangent_continuous.comp continuous_fst).prodMk continuous_snd)

theorem hasDerivAt_contour_value {shape : ℝ → PeriodicC1HolderHalf}
    {velocity : PeriodicC1HolderHalf} {time : ℝ}
    (equation : HasDerivAt shape velocity time) (label : ℝ) :
    HasDerivAt (fun parameter => (shape parameter).val.1 label) (velocity.val.1 label) time := by
  have result := ((contourLabelEvaluation label).hasFDerivAt (x := shape time)).comp_hasDerivAt time equation
  exact result

theorem hasDerivAt_contour_tangent {shape : ℝ → PeriodicC1HolderHalf}
    {velocity : PeriodicC1HolderHalf} {time : ℝ}
    (equation : HasDerivAt shape velocity time) (label : ℝ) :
    HasDerivAt (fun parameter => (shape parameter).val.2.val.1 label) (velocity.val.2.val.1 label) time := by
  have result := ((contourTangentEvaluation label).hasFDerivAt (x := shape time)).comp_hasDerivAt time equation
  exact result

end

end EulerNonuniqueness.Paper
