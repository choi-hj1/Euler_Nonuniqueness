import EulerNonuniqueness.Section3.CanonicalInteractionParameter
import EulerNonuniqueness.General.RightMovingNormSlope

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem canonicalNormalizedInteractionCoordinate_exists_uniform_moving_parameter_slope :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        {frequency left right time distance weight : ℝ}, frequency ≠ 0 → time ∈ Ioo left right →
      0 < distance → 0 ≤ weight → 48 * (family.patch index).radius ≤ distance →
      (∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
        ∀ position ∈ (family.patch source).domain current,
        distance ≤ ‖(family.patch index).center current - position‖) →
      (∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) current)
        ((family.patch index).center current) position) ≤ weight) →
      weight / |frequency| ≤ radius →
      ∀ (curve angular : ℝ → PeriodicC1HolderHalf) (angularVelocity : PeriodicC1HolderHalf),
      ContinuousAt curve time → HasDerivAt angular angularVelocity time →
      ‖curve time - standardCircleBanach‖ < radius → ‖angular time‖ < radius →
      (∀ current ∈ Ioo left right, ∀ label, star ((angular current).val.1 label) = (angular current).val.1 label) →
      ∀ frozenRate threshold : ℝ,
      (∀ bound : ℝ, frozenRate < bound → ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖family.canonicalNormalizedInteractionCoordinate index (angular time)
          frequency current (curve current)‖) time later < bound) →
      frozenRate + constant * (weight / |frequency|) * ‖angularVelocity‖ < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖family.canonicalNormalizedInteractionCoordinate index (angular current)
          frequency current (curve current)‖) time later < threshold := by
  obtain ⟨radius, positive, constant, one, parameters⟩ :=
    canonicalNormalizedInteractionCoordinate_exists_uniform_parameter_bound
  refine ⟨radius, positive, constant, one, ?_⟩
  intro count family index frequency left right time distance weight nonzero member distancePositive
    weightNonnegative small separated weightBounds frequencySmall curve angular angularVelocity
    curveContinuous angularDerivative curveSmall angularSmall angularReal frozenRate threshold frozenBound strict
  let admissible : Set PeriodicC1HolderHalf := {parameter | ‖parameter‖ ≤ radius ∧
    ∀ label, star (parameter.val.1 label) = parameter.val.1 label}
  have curveNear : ∀ᶠ later in 𝓝 time, ‖curve later - standardCircleBanach‖ < radius :=
    (curveContinuous.sub continuousAt_const).norm.eventually (gt_mem_nhds curveSmall)
  have angularNear : ∀ᶠ later in 𝓝 time, ‖angular later‖ < radius :=
    angularDerivative.continuousAt.norm.eventually (gt_mem_nhds angularSmall)
  have intervalNear : ∀ᶠ later in 𝓝 time, later ∈ Ioo left right := Ioo_mem_nhds member.1 member.2
  have variation : ∀ᶠ later in 𝓝[>] time,
      ∀ first ∈ admissible, ∀ second ∈ admissible,
      ‖family.canonicalNormalizedInteractionCoordinate index first frequency later (curve later) -
        family.canonicalNormalizedInteractionCoordinate index second frequency later (curve later)‖ ≤
          constant * (weight / |frequency|) * ‖first - second‖ := by
    filter_upwards [curveNear.filter_mono nhdsWithin_le_nhds, intervalNear.filter_mono nhdsWithin_le_nhds]
      with later nearby inside
    intro first firstInside second secondInside
    exact parameters family index first second firstInside.1 secondInside.1 firstInside.2 secondInside.2
      nonzero distancePositive weightNonnegative small (separated later inside) (weightBounds later inside)
      frequencySmall (curve later) nearby.le
  have initialInside : angular time ∈ admissible := ⟨angularSmall.le, angularReal time member⟩
  have nearbyInside : ∀ᶠ later in 𝓝[>] time, angular later ∈ admissible := by
    filter_upwards [angularNear.filter_mono nhdsWithin_le_nhds, intervalNear.filter_mono nhdsWithin_le_nhds]
      with later nearby inside
    exact ⟨nearby.le, angularReal later inside⟩
  exact EulerNonuniqueness.General.eventually_right_moving_norm_slope_lt
    variation angularDerivative initialInside nearbyInside frozenBound strict

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
