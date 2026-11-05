import EulerNonuniqueness.Section5.CascadeInitialGeometry
import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialBoundary
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion

noncomputable section

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem cascadeInitialDisks_of_circle_initial_state
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    (scales : Scales) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    (phase unstable : Fin count → ℝ) (dipoleAngle : ℕ → ℝ)
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon
      (0, (fun label => cascadeInitialCenter scales orbit sectionTime phase unstable (dipoleAngle count)
        (finProdFinEquiv.symm label)), fun _ => standardCircleBanach))
    (radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (reference : PatchMotion count) (initial : ReferenceInitialDisks scales reference phase unstable (1 / 2)) :
    CascadeInitialDisks scales orbit sectionTime dipoleAngle reference trajectory.movingFamily.patchMotion := by
  have circles : ∀ label : Fin (count * 4),
      ((0 : ℝ), (fun label => cascadeInitialCenter scales orbit sectionTime phase unstable (dipoleAngle count)
        (finProdFinEquiv.symm label)), fun _ => standardCircleBanach).2.2 label = standardCircleBanach := fun _ => rfl
  have domains (index : Fin count) (patch : Fin 4) := trajectory.movingPatch_domain_initial_circle circles
    (finProdFinEquiv (index, patch))
  have boundaries (index : Fin count) (patch : Fin 4) := trajectory.movingPatch_boundary_initial_circle
    rfl circles (finProdFinEquiv (index, patch))
  constructor
  · intro index below patch
    have notLast : index.val + 1 ≠ count := by omega
    constructor
    · change (trajectory.movingPatch (finProdFinEquiv (index, patch))).domain 0 = _
      rw [domains, radiusIdentity, (initial index).2 patch |>.1]
      simp only [cascadeInitialCenter, Equiv.symm_apply_apply, Prod.fst, Prod.snd, if_neg notLast]
    · funext angle
      change (trajectory.movingPatch (finProdFinEquiv (index, patch))).boundary 0 angle = _
      rw [boundaries, radiusIdentity, (initial index).2 patch |>.2 angle]
      simp only [cascadeInitialCenter, Equiv.symm_apply_apply, Prod.fst, Prod.snd, if_neg notLast]
  · intro index last patch
    constructor
    · change (trajectory.movingPatch (finProdFinEquiv (index, patch))).domain 0 = _
      rw [domains, radiusIdentity]
      simp only [cascadeInitialCenter, Equiv.symm_apply_apply, Prod.fst, Prod.snd, if_pos last, last, if_true]
    · intro angle
      change (trajectory.movingPatch (finProdFinEquiv (index, patch))).boundary 0 angle = _
      rw [boundaries, radiusIdentity]
      simp only [cascadeInitialCenter, Equiv.symm_apply_apply, Prod.fst, Prod.snd, if_pos last, last, if_true]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
