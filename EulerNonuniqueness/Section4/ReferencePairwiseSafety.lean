import EulerNonuniqueness.Section4.ReferencePairCenterVelocity
import EulerNonuniqueness.Section4.ReferenceInitialInvariants
import EulerNonuniqueness.Section6.MovingQuadrupoleAngularMoment
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem reference_pair_center_change_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon finish error tolerance threshold : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonNonnegative : 0 ≤ horizon) (timeRange : Icc 0 finish ⊆ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales family.patchMotion phase unstable threshold)
    (inside : ∀ time ∈ Icc 0 finish, ∀ index,
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 finish, ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (differenceLower : ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (differenceUpper : ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ time ∈ Icc 0 finish, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ time ∈ Icc 0 finish, ∀ index,
      ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ time ∈ Icc 0 finish, ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖)
    (centerUpper : ∀ time ∈ Icc 0 finish, ∀ receiver source : Fin count, receiver ≠ source →
      ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖ ≤
        2 * |scales.location (receiver.val + 1) - scales.location (source.val + 1)|)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (control : ∀ time ∈ Icc 0 finish, ∀ index patch,
      BoundaryCloseToCircle scales family.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (toleranceNonnegative : 0 ≤ tolerance)
    (omegaLength : ∀ index : Fin count,
      scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ tolerance * scales.location (index.val + 1)) :
    ∀ time ∈ Icc 0 finish, ∀ first second : Fin count, first ≠ second →
      ‖(quadrupoleCenter family.patchMotion time first - quadrupoleCenter family.patchMotion time second) -
          ((scales.location (first.val + 1) : ℂ) - (scales.location (second.val + 1) : ℂ))‖ ≤
        ((15120 / Real.pi) * scales.strain + 1800 * tolerance) *
          |scales.location (first.val + 1) - scales.location (second.val + 1)| * time := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  intro time member first second different
  have derivative (current : ℝ) (currentInside : current ∈ Icc 0 finish) :=
    (family.quadrupoleCenter_differentiableAt (inside current currentInside) (material current currentInside) first).hasDerivAt.sub
      (family.quadrupoleCenter_differentiableAt (inside current currentInside) (material current currentInside) second).hasDerivAt
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current currentInside => (derivative current currentInside).hasDerivWithinAt)
    (fun current currentInside => family.reference_pair_center_velocity_bound scales densityEquation evolution
      (timeRange ⟨currentInside.1, currentInside.2.le⟩) amplitudePositive frequencyBound ratioBound alphaPositive
      (inside current ⟨currentInside.1, currentInside.2.le⟩) (material current ⟨currentInside.1, currentInside.2.le⟩)
      (differenceLower current ⟨currentInside.1, currentInside.2.le⟩)
      (differenceUpper current ⟨currentInside.1, currentInside.2.le⟩)
      (radialSmall current ⟨currentInside.1, currentInside.2.le⟩)
      (asymmetrySmall current ⟨currentInside.1, currentInside.2.le⟩)
      (centerSeparation current ⟨currentInside.1, currentInside.2.le⟩)
      (centerUpper current ⟨currentInside.1, currentInside.2.le⟩) lengthSmall
      (control current ⟨currentInside.1, currentInside.2.le⟩) errorNonnegative errorSmall radiusSmall
      toleranceNonnegative omegaLength first second different) time member
  rw [(evolution.reference_initial_center_and_asymmetry horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial first).1,
    (evolution.reference_initial_center_and_asymmetry horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial second).1,
    sub_zero] at estimate
  exact estimate

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
