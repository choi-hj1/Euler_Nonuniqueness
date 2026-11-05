import EulerNonuniqueness.Section6.MovingInversePowerRegularity
import EulerNonuniqueness.Section4.ReferenceForeignStrainIdentity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem subfamilyComplexStrain_contDiffAt_of_local_center {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) {time distance : ℝ}
    (centerSmooth : ContDiffAt ℝ 1 center time)
    (inside : ∀ source ∈ selected, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (distancePositive : 0 < distance)
    (separatedNear : ∀ᶠ current in 𝓝 time, ∀ source ∈ selected,
      ∀ position ∈ (family.patch source).domain current, distance ≤ ‖center current - position‖) :
    ContDiffAt ℝ 1 (fun current => vorticityComplexStrain
      (family.subfamilyVorticity selected current) (center current)) time := by
  have regular := family.exteriorTaylorCoefficient_contDiffAt_of_local_center selected center 1 1
    centerSmooth inside (fun _ => distance) (fun _ _ => distancePositive) separatedNear
  apply regular.congr_of_eventuallyEq
  filter_upwards [separatedNear] with current separated
  rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center 1 current 0
    distancePositive separated]
  exact (exteriorVorticityCoefficient_zero_eq_complexStrain _ _ _).symm

theorem subfamilyComplexStrain_continuousOn_of_center_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (times : Set ℝ) {distance : ℝ} (distancePositive : 0 < distance)
    (centerSmooth : ∀ time ∈ times, ContDiffAt ℝ 1 center time)
    (inside : ∀ time ∈ times, ∀ source ∈ selected,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (centerGaps : ∀ time ∈ times, ∀ source ∈ selected,
      distance + 3 * (family.patch source).radius ≤ ‖center time - (family.patch source).center time‖) :
    ContinuousOn (fun current => vorticityComplexStrain
      (family.subfamilyVorticity selected current) (center current)) times := by
  intro time member
  apply (family.subfamilyComplexStrain_contDiffAt_of_local_center selected center
    (centerSmooth time member) (inside time member) distancePositive ?_).continuousAt.continuousWithinAt
  apply (eventually_all_finset selected).mpr
  intro source sourceMember
  have strictGap : distance + 2 * (family.patch source).radius <
      ‖center time - (family.patch source).center time‖ := by
    linarith [(family.patch source).radius_positive, centerGaps time member source sourceMember]
  have normContinuous : ContinuousAt (fun current => ‖center current - (family.patch source).center current‖) time :=
    ((centerSmooth time member).continuousAt.sub (family.patch source).center_continuous.continuousAt).norm
  filter_upwards [normContinuous.eventually (Ioi_mem_nhds strictGap)] with current large
  intro position positionMember
  have sourceBound : ‖position - (family.patch source).center current‖ < 2 * (family.patch source).radius := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      (family.patch source).domain_subset_ball_two_radius current positionMember
  have triangle := norm_add_le (center current - position) (position - (family.patch source).center current)
  rw [sub_add_sub_cancel] at triangle
  linarith

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
