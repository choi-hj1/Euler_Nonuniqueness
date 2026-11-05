import EulerNonuniqueness.Section3.C1HolderInverse
import EulerNonuniqueness.Section3.C1HolderContinuousOperations
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus
import Mathlib.Analysis.Analytic.Constructions

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance c1InverseAnalyticGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance c1InverseAnalyticSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance c1InverseAnalyticOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance c1InverseAnalyticOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance c1InverseAnalyticOperatorRing : NormedRing (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedRing (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance c1InverseAnalyticOperatorAlgebra : NormedAlgebra ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAlgebra (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance c1InverseAnalyticUniformGroup : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance c1InverseAnalyticOperatorComplete : CompleteSpace (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.instCompleteSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)

def c1MultiplierUnit (data : PeriodicC1HolderHalf) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) : (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)ˣ where
  val := c1ProductCLM data
  inv := c1ProductCLM (c1Inverse data positive separated)
  val_inv := by
    apply ContinuousLinearMap.ext
    intro value
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change data.val.1 label * ((data.val.1 label)⁻¹ * value.val.1 label) = value.val.1 label
    rw [← mul_assoc, mul_inv_cancel₀, one_mul]
    exact norm_ne_zero_iff.mp (ne_of_gt (positive.trans_le (separated label)))
  inv_val := by
    apply ContinuousLinearMap.ext
    intro value
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (data.val.1 label)⁻¹ * (data.val.1 label * value.val.1 label) = value.val.1 label
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    exact norm_ne_zero_iff.mp (ne_of_gt (positive.trans_le (separated label)))

def extendedC1Inverse (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  (Ring.inverse (c1ProductCLM data)) (c1Constant 1)

theorem extendedC1Inverse_eq (data : PeriodicC1HolderHalf) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    extendedC1Inverse data = c1Inverse data positive separated := by
  have inverse := Ring.inverse_unit (c1MultiplierUnit data positive separated)
  change Ring.inverse (c1ProductCLM data) = c1ProductCLM (c1Inverse data positive separated) at inverse
  unfold extendedC1Inverse
  rw [inverse]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (data.val.1 label)⁻¹ * 1 = (data.val.1 label)⁻¹
  exact mul_one _

theorem extendedC1Inverse_value (data : PeriodicC1HolderHalf) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (label : ℝ) :
    (extendedC1Inverse data).val.1 label = (data.val.1 label)⁻¹ := by
  rw [extendedC1Inverse_eq data positive separated, c1Inverse_value]

theorem analyticAt_extendedC1Inverse (data : PeriodicC1HolderHalf) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) : AnalyticAt ℝ extendedC1Inverse data := by
  have inverse : AnalyticAt ℝ Ring.inverse (c1ProductCLM data) :=
    analyticAt_inverse (𝕜 := ℝ) (A := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      (c1MultiplierUnit data positive separated)
  have multiplier : AnalyticAt ℝ
      (fun current : PeriodicC1HolderHalf => Ring.inverse (c1ProductCLM current)) data :=
    inverse.comp (c1ProductCLM.analyticAt data)
  unfold extendedC1Inverse
  exact ((ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf (c1Constant 1)).analyticAt _).comp multiplier

theorem extendedC1Inverse_one : extendedC1Inverse (c1Constant 1) = c1Constant 1 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [extendedC1Inverse_value (c1Constant 1) (show (0 : ℝ) < 1 by norm_num)
    (fun position => by change (1 : ℝ) ≤ ‖(1 : ℂ)‖; norm_num)]
  change (1 : ℂ)⁻¹ = 1
  norm_num

theorem extendedC1Inverse_hasLipschitzDerivativeNear_one :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear extendedC1Inverse (c1Constant 1) := by
  exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt
    (analyticAt_extendedC1Inverse (c1Constant 1) (show (0 : ℝ) < 1 by norm_num)
      (fun position => by change (1 : ℝ) ≤ ‖(1 : ℂ)‖; norm_num))

end EulerNonuniqueness.Paper
