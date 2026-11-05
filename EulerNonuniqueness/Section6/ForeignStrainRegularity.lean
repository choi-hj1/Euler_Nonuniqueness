import EulerNonuniqueness.Section6.MovingInversePowerRegularity
import EulerNonuniqueness.Section6.ForeignQuadrupoleStrainDerivative

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem foreignQuadrupoleStrain_contDiffAt {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (index : Fin count) {time distance : ℝ}
    (inside : ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (distancePositive : 0 < distance)
    (centerGaps : ∀ source ∈ foreignQuadrupolePatchLabels index,
      distance + 3 * (family.patch source).radius ≤
        ‖quadrupoleCenter family.patchMotion time index - (family.patch source).center time‖) :
    ContDiffAt ℝ 1 (family.foreignQuadrupoleStrain index) time := by
  let center : ℝ → ℂ := fun current => quadrupoleCenter family.patchMotion current index
  have centerSmooth := family.quadrupoleCenter_contDiffAt index (fun _ => inside _)
  have individual : ∀ source ∈ foreignQuadrupolePatchLabels index, ∀ᶠ current in 𝓝 time,
      ∀ position ∈ (family.patch source).domain current, distance ≤ ‖center current - position‖ := by
    intro source member
    have strictGap : distance + 2 * (family.patch source).radius <
        ‖center time - (family.patch source).center time‖ := by
      dsimp only [center]
      linarith [(family.patch source).radius_positive, centerGaps source member]
    have normContinuous : ContinuousAt (fun current => ‖center current - (family.patch source).center current‖) time :=
      (centerSmooth.continuousAt.sub (family.patch source).center_continuous.continuousAt).norm
    filter_upwards [normContinuous.eventually (Ioi_mem_nhds strictGap)] with current large
    intro position positionInside
    have sourceBound : ‖position - (family.patch source).center current‖ < 2 * (family.patch source).radius := by
      simpa only [Metric.mem_ball, dist_eq_norm] using
        (family.patch source).domain_subset_ball_two_radius current positionInside
    have triangle := norm_add_le (center current - position) (position - (family.patch source).center current)
    rw [sub_add_sub_cancel] at triangle
    linarith
  exact family.exteriorTaylorCoefficient_contDiffAt_of_local_center (foreignQuadrupolePatchLabels index) center 1 1
    centerSmooth (fun source _ => inside source) (fun _ => distance) (fun _ _ => distancePositive)
    ((eventually_all_finset (foreignQuadrupolePatchLabels index)).mpr individual)

theorem foreignQuadrupoleStrainDerivative_continuousOn {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (index : Fin count) (times : Set ℝ)
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (inside : ∀ time ∈ times, ∀ source,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ time ∈ times, ∀ source ∈ foreignQuadrupolePatchLabels index, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (distance : ℝ → ℝ) (positive : ∀ time ∈ times, 0 < distance time)
    (centerGaps : ∀ time ∈ times, ∀ source ∈ foreignQuadrupolePatchLabels index,
      distance time + 3 * (family.patch source).radius ≤
        ‖quadrupoleCenter family.patchMotion time index - (family.patch source).center time‖) :
    ContinuousOn (family.foreignQuadrupoleStrainDerivative scales index) times := by
  have derivativeContinuous : ContinuousOn (deriv (family.foreignQuadrupoleStrain index)) times := by
    intro time member
    have smooth := family.foreignQuadrupoleStrain_contDiffAt index (inside time member)
      (positive time member) (centerGaps time member)
    have differentialContinuous : ContinuousAt (fderiv ℝ (family.foreignQuadrupoleStrain index)) time :=
      (smooth.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp differentialContinuous).continuousWithinAt
  apply derivativeContinuous.congr
  intro time member
  exact (family.foreignQuadrupoleStrain_hasDerivAt scales index densityEquation (inside time member)
    (material time member) (positive time member) (centerGaps time member)).deriv.symm

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
