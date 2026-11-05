import EulerNonuniqueness.Section3.MovingMaterialInitialDisks
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem referenceInitialDisks_of_initial_circles {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (phase unstable : Fin count → ℝ) (threshold : ℝ)
    (shootingBound : ∀ index, |unstable index| ≤ threshold)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4),
      (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1))
    (centerIdentity : ∀ (index : Fin count) (patch : Fin 4),
      (family.patch (finProdFinEquiv (index, patch))).center 0 =
        initialDiskCenter scales (index.val + 1) (phase index) (unstable index) patch)
    (initialCircle : ∀ label, (family.patch label).shape 0 = standardCircleBanach)
    (initialRotation : ∀ label, Circle.exp ((family.patch label).phase 0) = 1) :
    ReferenceInitialDisks scales family.patchMotion phase unstable threshold := by
  intro index
  refine ⟨shootingBound index, fun patch => ⟨?_, ?_⟩⟩
  · change (family.patch (finProdFinEquiv (index, patch))).domain 0 = _
    rw [(family.patch (finProdFinEquiv (index, patch))).domain_eq_ball_of_circle
      (initialCircle (finProdFinEquiv (index, patch))), centerIdentity, radiusIdentity]
  · intro angle
    change (family.patch (finProdFinEquiv (index, patch))).boundary 0 angle = _
    rw [MovingMaterialPatch.boundary, initialCircle, centerIdentity, radiusIdentity, initialRotation]
    simp only [Circle.coe_one, one_mul]
    change initialDiskCenter scales (index.val + 1) (phase index) (unstable index) patch +
      scales.radius (index.val + 1) • Complex.exp ((angle : ℂ) * Complex.I) = _
    rw [Complex.real_smul, mul_comm (angle : ℂ) Complex.I]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
