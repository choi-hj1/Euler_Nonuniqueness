import EulerNonuniqueness.Section3.MovingCanonicalCentroidResponse
import EulerNonuniqueness.Section6.MovingPatchVelocityCentroidCorrection

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.biotSavart_subfamily_eq_centroid_and_corrections
    {count : ℕ} (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (receiver : ℂ) (time : ℝ) :
    biotSavart (family.subfamilyVorticity selected time) receiver =
      (∑ source ∈ selected,
        (family.density source * volume.real ((family.patch source).domain time)) •
          biotSavartKernel (receiver - (family.patch source).center time)) +
      ∑ source ∈ selected,
        (family.patch source).sourceVelocityCentroidCorrection (family.density source) receiver time := by
  rw [family.biotSavart_subfamily_eq_sum]
  simp_rw [FiniteMovingPatchFamily.patchVorticity,
    MovingMaterialPatch.sourceVelocity_eq_centroid_and_correction]
  rw [Finset.sum_add_distrib]

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem centerVelocity_eq_point_and_two_corrections
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0)
    (initialCentered : ∀ index, contourCentroidFunctional (initial.2.2 index) = 0)
    (marginPositive : 0 < margin) {horizon time distance : ℝ}
    (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (nonnegativeTime : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count) (positive : 0 < distance) (small : 8 * (trajectory.movingFamily.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
      distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖)
    (area : contourAreaFunctional ((trajectory.curve time).2.2 index) = Real.pi)
    (ratio : 24 * (trajectory.movingFamily.patch index).radius / distance < 1) :
    (trajectory.velocity time).2.1 index =
      (∑ source ∈ Finset.univ.erase index,
        (trajectory.movingFamily.density source *
          volume.real ((trajectory.movingFamily.patch source).domain time)) •
          biotSavartKernel ((trajectory.movingFamily.patch index).center time -
            (trajectory.movingFamily.patch source).center time)) +
      (∑ source ∈ Finset.univ.erase index,
        (trajectory.movingFamily.patch source).sourceVelocityCentroidCorrection
          (trajectory.movingFamily.density source) ((trajectory.movingFamily.patch index).center time) time) +
      configuration.radius index • ((Circle.exp (configuration.density index * time / 2) : ℂ) *
        contourExteriorCentroidResponse (Circle.exp (configuration.density index * time / 2))
          (fun power => trajectory.movingFamily.exteriorTaylorCoefficient (Finset.univ.erase index)
            (trajectory.movingFamily.patch index).center (trajectory.movingFamily.patch index).radius (power + 1) time)
          ((trajectory.curve time).2.2 index)) := by
  rw [trajectory.centerVelocity_eq_exterior_value_and_response initialClock initialCentered marginPositive
    inside nonnegativeTime safe index positive small separated area ratio,
    trajectory.movingFamily.biotSavart_subfamily_eq_centroid_and_corrections]

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
