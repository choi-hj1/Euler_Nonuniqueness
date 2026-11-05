import EulerNonuniqueness.Section3.MovingContourConfinementTube

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

open EulerNonuniqueness.Section6

theorem exists_materialNeighborhood_of_strict_margin
    {count : ℕ} {configuration : FiniteContourConfiguration count}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach) (marginPositive : 0 < margin)
    (index : Fin count) {time distance weight mass : ℝ}
    (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (strict : margin < infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (geometry : ∀ᶠ current in 𝓝 time,
      (∀ source ∈ Finset.univ.erase index, distance + 3 * (trajectory.movingFamily.patch source).radius ≤
        ‖(trajectory.movingFamily.patch index).center current - (trajectory.movingFamily.patch source).center current‖) ∧
      (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) current)
        ((trajectory.movingFamily.patch index).center current) position) ≤ weight ∧
      (∫ position, |trajectory.movingFamily.patchVorticity current index position|) ≤ mass) :
    Nonempty (ContourMaterialNeighborhood trajectory index time distance weight mass) := by
  have safeNear : ∀ᶠ current in 𝓝 time,
      margin < infDist (trajectory.curve current) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ :=
    ((continuous_infDist_pt _).comp trajectory.continuous).continuousAt.eventually (lt_mem_nhds strict)
  have intervalNear : ∀ᶠ current in 𝓝 time, current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    Ioo_mem_nhds inside.1 inside.2
  obtain ⟨radius, positive, contained⟩ := Metric.eventually_nhds_iff.mp
    (intervalNear.and (safeNear.and geometry))
  have near (current : ℝ) (member : current ∈ Ioo (time - radius) (time + radius)) : dist current time < radius := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [member.1, member.2]
  refine ⟨{
    left := time - radius
    right := time + radius
    member := ⟨by linarith, by linarith⟩
    inside := fun current member source => contained (near current member) |>.1
    material := fun current member source label => trajectory.movingFamily_material_equation_of_margin marginPositive
      (contained (near current member)).1 (contained (near current member)).2.1.le source label
    centered := ?_
    centerGaps := fun current member => (contained (near current member)).2.2.1
    weightBound := fun current member => (contained (near current member)).2.2.2.1
    massBound := fun current member => (contained (near current member)).2.2.2.2 }⟩
  intro current member
  filter_upwards [Ioo_mem_nhds (contained (near current member)).1.1 (contained (near current member)).1.2]
    with later laterInside
  exact (trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles laterInside index).symm

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
