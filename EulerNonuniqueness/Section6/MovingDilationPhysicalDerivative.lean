import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics
import EulerNonuniqueness.Section6.PaperDilationForcingParts

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem FiniteMovingPatchFamily.diagonalDifference_hasDerivAt_physical_rate
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (pathInside : ∀ patch, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (noncollision : FourPointNoncollision (fun patch => patchCentroid family.patchMotion time index patch)) :
    HasDerivAt (fun current => diagonalDifference family.patchMotion current index)
      (quadrupoleInternalDilationRate scales family.patchMotion index time +
        quadrupoleExternalDilationRate scales family.patchMotion index time +
        quadrupolePatchDilationRate scales family.patchMotion index time) time := by
  let positions : FourPointConfiguration := fun patch => patchCentroid family.patchMotion time index patch
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let external : FourPointConfiguration := fun patch =>
    biotSavart (externalPatchVorticity scales family.patchMotion time index) (positions patch)
  let errors := quadrupoleDilationPatchError scales family.patchMotion index time
  let velocity := fourPointField coefficient positions + external + errors
  have point (patch : Fin 4) : HasDerivAt (fun current => patchCentroid family.patchMotion current index patch)
      (velocity patch) time := by
    have actual := family.patchCentroid_hasDerivAt_point_field evolution inside index patch (pathInside patch) (material patch)
    convert actual using 1 <;> dsimp only [velocity, errors, external, positions, coefficient,
      quadrupoleDilationPatchError, Pi.add_apply] <;> abel
  have positive := ((point 0).sub (point 1)).div_const (2 : ℂ)
  have negative := ((point 2).sub (point 3)).div_const (2 : ℂ)
  have direct := positive.norm_sq.sub negative.norm_sq
  have direct' : HasDerivAt (fun current => diagonalDifference family.patchMotion current index)
      (fourPointDilationDirectionalRate positions velocity) time := direct
  have fieldIdentity := fourPointDilationDirectionalRate_field_eq_centered coefficient positions noncollision
  have centered := fourPointDilationDirectionalRate_velocity_centered positions external
    (biotSavart (externalPatchVorticity scales family.patchMotion time index)
      (quadrupoleCenter family.patchMotion time index))
  have rateIdentity : fourPointDilationDirectionalRate positions velocity =
      quadrupoleInternalDilationRate scales family.patchMotion index time +
        quadrupoleExternalDilationRate scales family.patchMotion index time +
        quadrupolePatchDilationRate scales family.patchMotion index time := by
    rw [show velocity = fourPointField coefficient positions + external + errors from rfl,
      fourPointDilationDirectionalRate_velocity_add, fourPointDilationDirectionalRate_velocity_add, fieldIdentity]
    change quadrupoleExternalDilationRate scales family.patchMotion index time =
      fourPointDilationDirectionalRate positions external at centered
    rw [← centered]
    rfl
  rw [rateIdentity] at direct'
  exact direct'

end EulerNonuniqueness.Paper
