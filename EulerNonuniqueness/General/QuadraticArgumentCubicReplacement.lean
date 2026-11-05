import Mathlib.Analysis.NormedSpace.Multilinear.Basic

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_bilinear_diagonal_sub_le (bilinear : Space →L[ℝ] Space →L[ℝ] Space)
    (first second : Space) :
    ‖bilinear first first - bilinear second second‖ ≤
      ‖bilinear‖ * ‖first - second‖ * (‖first‖ + ‖second‖) := by
  have identity : bilinear first first - bilinear second second =
      bilinear (first - second) first + bilinear second (first - second) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [identity]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖bilinear‖ * ‖first - second‖ * ‖first‖ + ‖bilinear‖ * ‖second‖ * ‖first - second‖ :=
      add_le_add (bilinear.le_opNorm₂ _ _) (bilinear.le_opNorm₂ _ _)
    _ = _ := by ring

theorem norm_bilinear_diagonal_sub_le_cubic (bilinear : Space →L[ℝ] Space →L[ℝ] Space)
    (relative transverse : Space) {bilinearBound meanBound : ℝ}
    (bilinearNonnegative : 0 ≤ bilinearBound) (meanNonnegative : 0 ≤ meanBound)
    (bounded : ‖bilinear‖ ≤ bilinearBound)
    (absorbed : ‖relative‖ ≤ 2 * ‖transverse‖)
    (quadraticDifference : ‖relative - transverse‖ ≤ meanBound * ‖transverse‖ ^ 2) :
    ‖bilinear relative relative - bilinear transverse transverse‖ ≤
      3 * bilinearBound * meanBound * ‖transverse‖ ^ 3 := by
  apply (norm_bilinear_diagonal_sub_le bilinear relative transverse).trans
  calc
    _ ≤ bilinearBound * (meanBound * ‖transverse‖ ^ 2) * (2 * ‖transverse‖ + ‖transverse‖) := by
      gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
