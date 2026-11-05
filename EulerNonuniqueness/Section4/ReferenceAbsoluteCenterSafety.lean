import EulerNonuniqueness.Section4.ReferenceAbsoluteCenterVelocity
import EulerNonuniqueness.Section4.ReferenceInitialInvariants
import EulerNonuniqueness.Section6.MovingQuadrupoleAngularMoment
import EulerNonuniqueness.Section1.UniformScaleBounds
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem reference_absolute_center_change_bound {count : ℕ}
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
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (control : ∀ time ∈ Icc 0 finish, ∀ index patch,
      BoundaryCloseToCircle scales family.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (omegaLength : ∀ index : Fin count, scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ tolerance) :
    ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      ‖quadrupoleCenter family.patchMotion time index - (scales.location (index.val + 1) : ℂ)‖ ≤
        (600 * tolerance + (3456 / Real.pi) * scales.strain +
          (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1)) * time := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  intro time member index
  have derivative (current : ℝ) (currentInside : current ∈ Icc 0 finish) :=
    (family.quadrupoleCenter_differentiableAt (inside current currentInside) (material current currentInside) index).hasDerivAt
  have bound (current : ℝ) (currentInside : current ∈ Ico 0 finish) :
      ‖deriv (fun next => quadrupoleCenter family.patchMotion next index) current‖ ≤
        600 * tolerance + (3456 / Real.pi) * scales.strain +
          (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) := by
    have closed : current ∈ Icc 0 finish := ⟨currentInside.1, currentInside.2.le⟩
    have estimate := family.reference_absolute_center_velocity_bound scales densityEquation evolution (timeRange closed)
      amplitudePositive frequencyBound ratioBound alphaPositive (inside current closed) (material current closed)
      (differenceLower current closed) (differenceUpper current closed) (radialSmall current closed)
      (asymmetrySmall current closed) (centerSeparation current closed) lengthSmall (control current closed)
      errorNonnegative errorSmall radiusSmall index
    apply estimate.trans
    have firstCost := mul_le_mul_of_nonneg_left (omegaLength index) (by norm_num : (0 : ℝ) ≤ 600)
    have secondCost := mul_le_mul_of_nonneg_left
      (scales.length_le_one frequencyPositive ratioPositive (index.val + 1))
      (by positivity : 0 ≤ (3456 / Real.pi) * scales.strain)
    have combined := add_le_add_right (add_le_add firstCost secondCost)
      ((48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1))
    convert combined using 1 <;> ring
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current currentInside => (derivative current currentInside).hasDerivWithinAt) bound time member
  rw [(evolution.reference_initial_center_and_asymmetry horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index).1,
    sub_zero] at estimate
  exact estimate

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
