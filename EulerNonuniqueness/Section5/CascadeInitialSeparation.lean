import EulerNonuniqueness.Section5.CascadeStatement
import EulerNonuniqueness.Section4.ReferenceInitialShapeCoordinates

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.cascade_terminal_initial_centroid
    {count : ℕ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime horizon : ℝ}
    {dipoleAngle : ℕ → ℝ} {reference alternative : PatchMotion count}
    (evolution : FinitePatchEvolution scales alternative horizon) (horizonNonnegative : 0 ≤ horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (initial : CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative)
    (index : Fin count) (last : index.val + 1 = count) (patch : Fin 4) :
    patchCentroid alternative 0 index patch =
      separatingInitialCenter scales orbit sectionTime (dipoleAngle count) count patch := by
  apply evolution.patchCentroid_eq_of_domain_eq_ball ⟨le_rfl, horizonNonnegative⟩ index patch _
    (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _)
  simpa only [last] using (initial.2 index last patch).1

theorem FinitePatchEvolution.cascade_terminal_firstSeparationTime
    {count : ℕ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime horizon : ℝ}
    {dipoleAngle : ℕ → ℝ} {reference alternative : PatchMotion count}
    (evolution : FinitePatchEvolution scales alternative horizon) (horizonNonnegative : 0 ≤ horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (initial : CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative)
    (index : Fin count) (last : index.val + 1 = count) :
    FirstSeparationTime scales orbit sectionTime alternative index 0 := by
  refine ⟨le_rfl, ?_, fun earlier nonnegative before => False.elim (not_lt_of_ge nonnegative before)⟩
  have centroids := evolution.cascade_terminal_initial_centroid horizonNonnegative amplitudePositive
    frequencyPositive ratioPositive initial index last
  unfold pairCenterDistance
  rw [centroids 0, centroids 3, centroids 1, centroids 2]
  have algebra :
      (separatingInitialCenter scales orbit sectionTime (dipoleAngle count) count 0 +
        separatingInitialCenter scales orbit sectionTime (dipoleAngle count) count 3) / 2 -
      (separatingInitialCenter scales orbit sectionTime (dipoleAngle count) count 1 +
        separatingInitialCenter scales orbit sectionTime (dipoleAngle count) count 2) / 2 =
      (scales.length count : ℂ) *
        Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ)) *
        (orbit.positive sectionTime - orbit.negative sectionTime) := by
    simp only [separatingInitialCenter,
      show (0 : Fin 4) = 0 from rfl,
      show (1 : Fin 4) ≠ 0 by decide, show (1 : Fin 4) = 1 from rfl,
      show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
      show (2 : Fin 4) = 2 from rfl,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 2 by decide, if_true, if_false]
    ring
  rw [algebra]
  have rotation : ‖Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (scales.length_pos count),
    rotation, mul_one, separationRadius, last]
  exact mul_comm _ _

end EulerNonuniqueness.Paper
