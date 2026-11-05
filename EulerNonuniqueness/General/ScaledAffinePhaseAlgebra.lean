import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem scaled_affine_value_phase_relation
    {frequency : ℝ} (nonzero : frequency ≠ 0)
    (generator : Space →L[ℝ] Space) (primitive leadingValue partner baseSource baseLeadingSource : Space)
    (valueEquation : partner = generator leadingValue + baseLeadingSource) :
    frequency • generator primitive + baseSource = partner +
      frequency • generator (primitive - frequency⁻¹ • leadingValue) + (baseSource - baseLeadingSource) := by
  rw [valueEquation, map_sub, map_smul, smul_sub, smul_smul, mul_inv_cancel₀ nonzero, one_smul]
  abel

theorem scaled_affine_leading_residual
    {frequency : ℝ} (nonzero : frequency ≠ 0)
    (generator correction phaseCorrection : Space →L[ℝ] Space)
    (source selfValue leadingValue partner relative : Space) :
    source + frequency • generator (frequency⁻¹ • leadingValue + (frequency⁻¹ • correction) relative) -
        (frequency⁻¹ • correction) (frequency • selfValue) - partner - phaseCorrection relative =
      source + generator (leadingValue + correction relative) - correction selfValue - partner - phaseCorrection relative := by
  simp only [ContinuousLinearMap.smul_apply, map_add, map_smul, smul_add, smul_smul,
    mul_inv_cancel₀ nonzero, inv_mul_cancel₀ nonzero, one_smul]

end EulerNonuniqueness.General
