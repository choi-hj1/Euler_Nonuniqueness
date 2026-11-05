import EulerNonuniqueness.General.BilinearOperatorCalculus

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem inverse_equivalence_half_bilinear
    (coordinates : Space ≃L[ℝ] Space) (second : BilinearEnd Space) (first last : Space) :
    coordinates.symm (second (coordinates first) (coordinates last)) =
      (2 : ℝ) • Ring.inverse coordinates.toContinuousLinearMap
        ((1 / 2 : ℝ) • second (coordinates first) (coordinates last)) := by
  have inverseIdentity : Ring.inverse coordinates.toContinuousLinearMap = coordinates.symm.toContinuousLinearMap :=
    Ring.inverse_unit coordinates.toUnit
  rw [inverseIdentity]
  change coordinates.symm (second (coordinates first) (coordinates last)) =
    (2 : ℝ) • coordinates.symm ((1 / 2 : ℝ) • second (coordinates first) (coordinates last))
  rw [map_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]

end EulerNonuniqueness.General
