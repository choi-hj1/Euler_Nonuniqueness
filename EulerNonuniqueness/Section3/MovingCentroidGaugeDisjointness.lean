import EulerNonuniqueness.Section3.MovingCentroidGaugeMaterial
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion
import EulerNonuniqueness.Section3.MovingMaterialPatchDisjointness

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem patchesDisjoint_on_interval
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    {horizon : ℝ} (beforeFinal : horizon < forwardHorizon) :
    PatchesDisjoint trajectory.movingFamily.patchMotion horizon := by
  intro time member index other patch otherPatch different
  let first := finProdFinEquiv (index, patch)
  let second := finProdFinEquiv (other, otherPatch)
  have distinct : first ≠ second := by
    intro equality
    have pair := finProdFinEquiv.injective equality
    obtain ⟨sameIndex, samePatch⟩ := Prod.mk.inj pair
    exact different.elim (fun contradiction => contradiction sameIndex) (fun contradiction => contradiction samePatch)
  have inside : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, member.1], member.2.trans_lt beforeFinal⟩
  change Disjoint ((trajectory.movingPatch first).domain time) ((trajectory.movingPatch second).domain time)
  apply MovingMaterialPatch.domains_disjoint_of_center_distance
  change 2 * configuration.radius first + 2 * configuration.radius second ≤ dist (trajectory.center first time) (trajectory.center second time)
  rw [trajectory.center_eq_curve inside first, trajectory.center_eq_curve inside second, dist_eq_norm]
  have separation := configuration.movingStateAdmissible_centers_separated trajectory.gap_positive (trajectory.admissible time) first second distinct
  linarith [configuration.radius_pos first, configuration.radius_pos second]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
