import Mathlib.Analysis.Calculus.VectorField

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def realForcingResidual (field forcing correction partner : Space → Space) (frequency : ℝ) (point : Space) : Space :=
  forcing point + fderiv ℝ field point (correction point) -
    fderiv ℝ correction point (field point) - frequency • partner point

theorem realForcingResidual_pullback (chart field forcing correction partner : Space → Space)
    (frequency : ℝ) (point : Space)
    (chartRegular : ContDiffAt ℝ 2 chart point)
    (fieldRegular : DifferentiableAt ℝ field (chart point))
    (correctionRegular : DifferentiableAt ℝ correction (chart point)) :
    VectorField.pullback ℝ chart (realForcingResidual field forcing correction partner frequency) point =
      realForcingResidual (VectorField.pullback ℝ chart field) (VectorField.pullback ℝ chart forcing)
        (VectorField.pullback ℝ chart correction) (VectorField.pullback ℝ chart partner) frequency point := by
  have bracket := VectorField.pullback_lieBracket (𝕜 := ℝ) (by simp : minSmoothness ℝ 2 ≤ 2)
    chartRegular correctionRegular fieldRegular
  change (fderiv ℝ chart point).inverse
      (forcing (chart point) + fderiv ℝ field (chart point) (correction (chart point)) -
        fderiv ℝ correction (chart point) (field (chart point)) - frequency • partner (chart point)) = _
  rw [show forcing (chart point) + fderiv ℝ field (chart point) (correction (chart point)) -
      fderiv ℝ correction (chart point) (field (chart point)) - frequency • partner (chart point) =
      forcing (chart point) + VectorField.lieBracket ℝ correction field (chart point) -
        frequency • partner (chart point) by
    simp only [VectorField.lieBracket]; abel]
  rw [map_sub, map_add, map_smul]
  change VectorField.pullback ℝ chart forcing point +
    VectorField.pullback ℝ chart (VectorField.lieBracket ℝ correction field) point -
      frequency • VectorField.pullback ℝ chart partner point = _
  rw [bracket]
  simp only [realForcingResidual, VectorField.lieBracket]
  abel

end EulerNonuniqueness.General
