import EulerNonuniqueness.Section3.PeriodicHilbertDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def periodicHilbertC1 (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions
    (periodicHilbertCLM (c1ValueHolder data)).val.1 (periodicHilbertCLM data.val.2).val.1
    (periodicHilbertCLM (c1ValueHolder data)).val.1.continuous
    (periodicHilbertCLM data.val.2).val.1.continuous
    ‖periodicHilbertCLM (c1ValueHolder data)‖ ‖periodicHilbertCLM data.val.2‖
    ‖periodicHilbertCLM data.val.2‖
    (PeriodicHolderHalf.value_bound _) (PeriodicHolderHalf.value_bound _)
    (PeriodicHolderHalf.holder_bound _) (periodicHilbertCLM_hasDerivAt data)
    (PeriodicHolderHalf.periodic _) (PeriodicHolderHalf.periodic _)

theorem periodicHilbertC1_value (data : PeriodicC1HolderHalf) (label : ℝ) :
    (periodicHilbertC1 data).val.1 label =
      (periodicHilbertCLM (c1ValueHolder data)).val.1 label := rfl

theorem periodicHilbertC1_tangent (data : PeriodicC1HolderHalf) :
    (periodicHilbertC1 data).val.2 = periodicHilbertCLM data.val.2 := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem periodicHilbertBound_nonneg : 0 ≤ periodicHilbertBound := by
  unfold periodicHilbertBound
  exact div_nonneg
    ((contourCauchySupConstant_nonneg standardCircleBanach standardCircleBanach_near).trans
      (le_max_left _ _)) Real.pi_pos.le

theorem periodicHilbertC1_norm_bound (data : PeriodicC1HolderHalf) :
    ‖periodicHilbertC1 data‖ ≤ 2 * periodicHilbertBound * ‖data‖ := by
  have valueBound : ‖periodicHilbertCLM (c1ValueHolder data)‖ ≤
      2 * periodicHilbertBound * ‖data‖ := by
    apply (periodicHilbertCLM_norm_bound _).trans
    exact (mul_le_mul_of_nonneg_left (c1ValueHolder_norm_bound data)
      periodicHilbertBound_nonneg).trans_eq (by ring)
  have tangentBound : ‖periodicHilbertCLM data.val.2‖ ≤
      2 * periodicHilbertBound * ‖data‖ := by
    apply (periodicHilbertCLM_norm_bound _).trans
    have component : ‖data.val.2‖ ≤ ‖data‖ := le_max_right _ _
    have estimate := mul_le_mul_of_nonneg_left component periodicHilbertBound_nonneg
    nlinarith [mul_nonneg periodicHilbertBound_nonneg (norm_nonneg data)]
  change max ‖(periodicHilbertC1 data).val.1‖ ‖(periodicHilbertC1 data).val.2‖ ≤ _
  apply max_le
  · apply (BoundedContinuousFunction.norm_le
      (mul_nonneg (mul_nonneg (by norm_num) periodicHilbertBound_nonneg) (norm_nonneg data))).mpr
    intro label
    exact (PeriodicHolderHalf.value_bound _ label).trans valueBound
  · rw [periodicHilbertC1_tangent]
    exact tangentBound

theorem periodicHilbertC1_add (first second : PeriodicC1HolderHalf) :
    periodicHilbertC1 (first + second) = periodicHilbertC1 first + periodicHilbertC1 second := by
  have embedding : c1ValueHolder (first + second) = c1ValueHolder first + c1ValueHolder second := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (periodicHilbertCLM (c1ValueHolder (first + second))).val.1 label = _
  rw [embedding, map_add]
  rfl

theorem periodicHilbertC1_smul (scalar : ℝ) (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (scalar • data) = scalar • periodicHilbertC1 data := by
  have embedding : c1ValueHolder (scalar • data) = scalar • c1ValueHolder data := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (periodicHilbertCLM (c1ValueHolder (scalar • data))).val.1 label = _
  rw [embedding]
  have identity := periodicHilbertCLM.toLinearMap.map_smul' scalar (c1ValueHolder data)
  change (periodicHilbertCLM (scalar • c1ValueHolder data)).val.1 label =
    scalar • (periodicHilbertCLM (c1ValueHolder data)).val.1 label
  exact congrArg (fun density : PeriodicHolderHalf => density.val.1 label) identity

def periodicHilbertC1CLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    { toFun := periodicHilbertC1
      map_add' := periodicHilbertC1_add
      map_smul' := periodicHilbertC1_smul }
    (2 * periodicHilbertBound) periodicHilbertC1_norm_bound

end

end EulerNonuniqueness.Paper
