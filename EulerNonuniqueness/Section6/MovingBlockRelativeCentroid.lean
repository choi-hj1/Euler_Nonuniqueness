import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem patchCentroid_sub_quadrupoleCenter_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (pathInside : ∀ patch, time ∈ Ioo
      (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label,
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales family.patchMotion time)
          ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (patch : Fin 4) :
    HasDerivAt (fun current => patchCentroid family.patchMotion current index patch -
      quadrupoleCenter family.patchMotion current index)
      ((∑ source : Fin 4,
        (patchAverageVelocity scales family.patchMotion time index patch
          (biotSavart (Paper.patchVorticity scales family.patchMotion time)) -
        patchAverageVelocity scales family.patchMotion time index source
          (biotSavart (Paper.patchVorticity scales family.patchMotion time)))) / 4) time := by
  have derivatives (source : Fin 4) := family.patchCentroid_hasDerivAt evolution inside index source
    (pathInside source) (material source)
  have center := (HasDerivAt.sum (u := Finset.univ) fun source _ => derivatives source).div_const 4
  have result := (derivatives patch).sub center
  convert result using 1
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem centered_four_velocity_norm_le (velocity : Fin 4 → ℂ) (patch : Fin 4) {bound : ℝ}
    (pairwise : ∀ source, ‖velocity patch - velocity source‖ ≤ bound) :
    ‖(∑ source : Fin 4, (velocity patch - velocity source)) / 4‖ ≤ bound := by
  rw [norm_div, Complex.norm_ofNat]
  have triangle := norm_sum_le (Finset.univ : Finset (Fin 4)) (fun source => velocity patch - velocity source)
  have total := Finset.sum_le_sum (fun source (_ : source ∈ (Finset.univ : Finset (Fin 4))) => pairwise source)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at total
  norm_num at total
  linarith

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
