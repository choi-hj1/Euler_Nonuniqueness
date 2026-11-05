import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

def linearHomologicalOperator (operator : Space →L[ℂ] Space) (frequency : ℂ)
    (correction : Space →L[ℂ] Space) : Space →L[ℂ] Space :=
  frequency • correction + correction.comp operator - operator.comp correction

def spectralHomologicalBlock (output input numerator : Space →L[ℂ] Space)
    (frequency outputEigenvalue inputEigenvalue : ℂ) : Space →L[ℂ] Space :=
  (frequency + inputEigenvalue - outputEigenvalue)⁻¹ • output.comp (numerator.comp input)

theorem spectralHomologicalBlock_equation
    (operator output input numerator : Space →L[ℂ] Space)
    (frequency outputEigenvalue inputEigenvalue : ℂ)
    (outputEigen : operator.comp output = outputEigenvalue • output)
    (inputEigen : input.comp operator = inputEigenvalue • input)
    (nonresonant : frequency + inputEigenvalue - outputEigenvalue ≠ 0) :
    linearHomologicalOperator operator frequency
      (spectralHomologicalBlock output input numerator frequency outputEigenvalue inputEigenvalue) =
      output.comp (numerator.comp input) := by
  apply ContinuousLinearMap.ext
  intro value
  have outputAt (current : Space) := congrArg (fun linear : Space →L[ℂ] Space => linear current) outputEigen
  have inputAt := congrArg (fun linear : Space →L[ℂ] Space => linear value) inputEigen
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] at outputAt inputAt
  simp only [linearHomologicalOperator, spectralHomologicalBlock, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, inputAt, outputAt]
  have scalar : frequency * (frequency + inputEigenvalue - outputEigenvalue)⁻¹ +
      (frequency + inputEigenvalue - outputEigenvalue)⁻¹ * inputEigenvalue -
      (frequency + inputEigenvalue - outputEigenvalue)⁻¹ * outputEigenvalue = 1 := by
    field_simp
  calc
    _ = (frequency * (frequency + inputEigenvalue - outputEigenvalue)⁻¹ +
        (frequency + inputEigenvalue - outputEigenvalue)⁻¹ * inputEigenvalue -
        (frequency + inputEigenvalue - outputEigenvalue)⁻¹ * outputEigenvalue) •
        output (numerator (input value)) := by module
    _ = _ := by rw [scalar, one_smul]

theorem spectralHomologicalBlock_norm_le
    (output input numerator : Space →L[ℂ] Space)
    (frequency outputEigenvalue inputEigenvalue : ℂ) :
    ‖spectralHomologicalBlock output input numerator frequency outputEigenvalue inputEigenvalue‖ ≤
      ‖(frequency + inputEigenvalue - outputEigenvalue)⁻¹‖ * ‖output‖ * ‖numerator‖ * ‖input‖ := by
  unfold spectralHomologicalBlock
  calc
    _ ≤ ‖(frequency + inputEigenvalue - outputEigenvalue)⁻¹‖ *
        ‖output.comp (numerator.comp input)‖ := norm_smul_le _ _
    _ ≤ ‖(frequency + inputEigenvalue - outputEigenvalue)⁻¹‖ *
        (‖output‖ * (‖numerator‖ * ‖input‖)) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by ring

end

end EulerNonuniqueness.General
