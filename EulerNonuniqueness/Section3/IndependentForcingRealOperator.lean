import EulerNonuniqueness.Section3.IndependentForcingRealification
import EulerNonuniqueness.Section3.IndependentRealForcingValue
import EulerNonuniqueness.General.RealLinearFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

local instance realCorrectionOperatorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance realCorrectionOperatorC1Semi : SeminormedAddCommGroup PeriodicC1HolderHalf :=
  realCorrectionOperatorC1Group.toSeminormedAddCommGroup

local instance realCorrectionRealOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem contourIndependentRealification_value (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (label : ℝ) : (contourIndependentRealification pair).val.1 label =
      pair.1.val.1 label + star (pair.2.val.1 label) := rfl

theorem realOperatorRealification_scaled_value (coefficient : ℂ)
    (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) (label : ℝ) :
    (contourIndependentRealification (coefficient • pair)).val.1 label =
      coefficient * pair.1.val.1 label + star (coefficient * pair.2.val.1 label) := rfl

def independentForcingRealCorrectionLinearMap (degree : ℕ) (coefficient : ℂ) :
    PeriodicC1HolderHalf →ₗ[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.realLinearFunction (independentForcingRealLinearCorrection degree coefficient)
    (independentForcingRealLinearCorrection_add degree coefficient)
    (independentForcingRealLinearCorrection_real_smul degree coefficient)

def independentForcingRealCorrectionCLM (degree : ℕ) (coefficient : ℂ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (independentForcingRealCorrectionLinearMap degree coefficient).mkContinuous
    (2 * ‖coefficient‖ * ‖independentForcingLinearCorrection degree‖)
    (independentForcingRealLinearCorrection_norm_le degree coefficient)

theorem independentForcingRealCorrectionCLM_apply (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) :
    independentForcingRealCorrectionCLM degree coefficient direction =
      contourIndependentRealification
        (coefficient • independentForcingLinearCorrection degree (contourIndependentEmbedding direction)) := by
  calc
    _ = independentForcingRealCorrectionLinearMap degree coefficient direction := by
      unfold independentForcingRealCorrectionCLM
      exact LinearMap.mkContinuous_apply (independentForcingRealCorrectionLinearMap degree coefficient)
        (2 * ‖coefficient‖ * ‖independentForcingLinearCorrection degree‖)
        (independentForcingRealLinearCorrection_norm_le degree coefficient) direction
    _ = independentForcingRealLinearCorrection degree coefficient direction := by
      unfold independentForcingRealCorrectionLinearMap
      with_reducible
        exact EulerNonuniqueness.General.realLinearFunction_apply
          (independentForcingRealLinearCorrection degree coefficient)
          (independentForcingRealLinearCorrection_add degree coefficient)
          (independentForcingRealLinearCorrection_real_smul degree coefficient) direction
    _ = _ := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rw [independentForcingRealLinearCorrection_value, realOperatorRealification_scaled_value]

theorem independentForcingRealCorrectionCLM_norm_le (degree : ℕ) (coefficient : ℂ) :
    ‖independentForcingRealCorrectionCLM degree coefficient‖ ≤
      2 * ‖coefficient‖ * ‖independentForcingLinearCorrection degree‖ := by
  with_reducible_and_instances
    unfold independentForcingRealCorrectionCLM
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end

end EulerNonuniqueness.Paper
