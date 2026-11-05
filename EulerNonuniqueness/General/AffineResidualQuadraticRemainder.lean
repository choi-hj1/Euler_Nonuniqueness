import Mathlib

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem affineResidual_remainder_identity
    (source currentSource selfCurrent selfBase value partner direction : Space)
    (generator currentGenerator correction partnerCorrection sourceDerivative : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space)
    (valueEquation : source + generator value - partner = 0)
    (selfZero : selfBase = 0) :
    currentSource + currentGenerator (value + correction direction) - correction selfCurrent -
      partner - partnerCorrection direction -
      (sourceDerivative direction + second direction value + generator (correction direction) -
        correction (generator direction) - partnerCorrection direction) =
      (currentSource - source - sourceDerivative direction) +
      (currentGenerator - generator - second direction) value +
      (currentGenerator - generator) (correction direction) -
      correction (selfCurrent - selfBase - generator direction) := by
  rw [selfZero, sub_zero, map_add, map_sub]
  simp only [ContinuousLinearMap.sub_apply]
  have canceled : partner = source + generator value := by
    exact (sub_eq_zero.mp valueEquation).symm
  rw [canceled]
  abel

theorem affineResidual_remainder_bound
    (source currentSource selfCurrent selfBase value partner direction : Space)
    (generator currentGenerator correction partnerCorrection sourceDerivative : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space)
    {sourceConstant derivativeConstant differenceConstant selfConstant : ℝ}
    (differenceNonnegative : 0 ≤ differenceConstant)
    (valueEquation : source + generator value - partner = 0) (selfZero : selfBase = 0)
    (sourceError : ‖currentSource - source - sourceDerivative direction‖ ≤ sourceConstant * ‖direction‖ ^ 2)
    (derivativeError : ‖currentGenerator - generator - second direction‖ ≤ derivativeConstant * ‖direction‖ ^ 2)
    (generatorDifference : ‖currentGenerator - generator‖ ≤ differenceConstant * ‖direction‖)
    (selfError : ‖selfCurrent - selfBase - generator direction‖ ≤ selfConstant * ‖direction‖ ^ 2) :
    ‖currentSource + currentGenerator (value + correction direction) - correction selfCurrent -
      partner - partnerCorrection direction -
      (sourceDerivative direction + second direction value + generator (correction direction) -
        correction (generator direction) - partnerCorrection direction)‖ ≤
      (sourceConstant + derivativeConstant * ‖value‖ +
        (differenceConstant + selfConstant) * ‖correction‖) * ‖direction‖ ^ 2 := by
  rw [affineResidual_remainder_identity source currentSource selfCurrent selfBase value partner direction
    generator currentGenerator correction partnerCorrection sourceDerivative second valueEquation selfZero]
  have first := ((currentGenerator - generator - second direction).le_opNorm value).trans
    (mul_le_mul_of_nonneg_right derivativeError (norm_nonneg value))
  have middle := ((currentGenerator - generator).le_opNorm (correction direction)).trans
    (mul_le_mul generatorDifference (correction.le_opNorm direction) (norm_nonneg _) (by positivity))
  have last := (correction.le_opNorm (selfCurrent - selfBase - generator direction)).trans
    (mul_le_mul_of_nonneg_left selfError (norm_nonneg correction))
  calc
    _ ≤ ‖currentSource - source - sourceDerivative direction‖ +
        ‖(currentGenerator - generator - second direction) value‖ +
        ‖(currentGenerator - generator) (correction direction)‖ +
        ‖correction (selfCurrent - selfBase - generator direction)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add₃_le) _)
    _ ≤ sourceConstant * ‖direction‖ ^ 2 + derivativeConstant * ‖direction‖ ^ 2 * ‖value‖ +
        (differenceConstant * ‖direction‖) * (‖correction‖ * ‖direction‖) +
        ‖correction‖ * (selfConstant * ‖direction‖ ^ 2) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
