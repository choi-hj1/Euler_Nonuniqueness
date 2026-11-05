import EulerNonuniqueness.Section3.CanonicalExteriorStaticPairRelative
import EulerNonuniqueness.Section3.ProjectedExteriorSeriesPairBounds

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  powerFirstJetOperatorGroup exteriorPowerSeriesOperatorSpace gaugeOperatorUniformSecondGroup

theorem canonicalProjectedExteriorContourField_exists_common_source_recipient_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
        (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
        (time firstDistance finalDistance : ℝ) (firstPositive : 0 < firstDistance) (finalPositive : 0 < finalDistance),
      ∀ (firstScale : 192 * (firstFamily.patch firstIndex).radius ≤ firstDistance)
        (finalScale : 192 * (finalFamily.patch finalIndex).radius ≤ finalDistance),
      ∀ (firstSeparated : ∀ source ∈ Finset.univ.erase firstIndex,
          ∀ position ∈ (firstFamily.patch source).domain time,
          firstDistance ≤ ‖(firstFamily.patch firstIndex).center time - position‖)
        (finalSeparated : ∀ source ∈ Finset.univ.erase finalIndex,
          ∀ position ∈ (finalFamily.patch source).domain time,
          finalDistance ≤ ‖(finalFamily.patch finalIndex).center time - position‖),
      ∀ (phase : Circle) (data : PeriodicC1HolderHalf), ‖data - standardCircleBanach‖ ≤ radius →
      ∀ operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf,
      ‖operator
        (firstFamily.canonicalProjectedExteriorContourField firstIndex time firstDistance firstPositive
            (by linarith [(firstFamily.patch firstIndex).radius_positive]) firstSeparated phase data -
          finalFamily.canonicalProjectedExteriorContourField finalIndex time finalDistance finalPositive
            (by linarith [(finalFamily.patch finalIndex).radius_positive]) finalSeparated phase data)‖ ≤
      constant * ‖operator‖ * (∑' degree, (96 : ℝ) ^ (degree + 1) *
        ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree -
          finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖) := by
  obtain ⟨radius, positive, smallRadius, constant, nonnegative, _, pair⟩ :=
    circleBasedProjectedExteriorSeries_exists_pair_value_bounds
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro firstCount finalCount firstFamily finalFamily firstIndex finalIndex time firstDistance finalDistance
    firstPositive finalPositive firstScale finalScale firstSeparated finalSeparated phase data nearby operator
  let increment := data - standardCircleBanach
  have incrementSmall : ‖increment‖ < 1 / 3 :=
    nearby.trans_lt (smallRadius.trans_lt (by norm_num))
  have firstRatio : 24 * (firstFamily.patch firstIndex).radius / firstDistance < 1 :=
    (div_lt_one firstPositive).mpr (by linarith [(firstFamily.patch firstIndex).radius_positive])
  have finalRatio : 24 * (finalFamily.patch finalIndex).radius / finalDistance < 1 :=
    (div_lt_one finalPositive).mpr (by linarith [(finalFamily.patch finalIndex).radius_positive])
  have firstSeries := firstFamily.canonicalProjectedExteriorContourField_eq_series firstIndex time firstDistance
    firstPositive (by linarith [(firstFamily.patch firstIndex).radius_positive]) firstSeparated phase increment incrementSmall firstRatio
  have finalSeries := finalFamily.canonicalProjectedExteriorContourField_eq_series finalIndex time finalDistance
    finalPositive (by linarith [(finalFamily.patch finalIndex).radius_positive]) finalSeparated phase increment incrementSmall finalRatio
  have reconstruct : standardCircleBanach + increment = data := by dsimp [increment]; abel
  rw [reconstruct] at firstSeries finalSeries
  have firstWeighted := firstFamily.canonicalExteriorStaticCoefficient_summable_weight96 firstIndex time firstDistance
    firstPositive firstScale firstSeparated
  have finalWeighted := finalFamily.canonicalExteriorStaticCoefficient_summable_weight96 finalIndex time finalDistance
    finalPositive finalScale finalSeparated
  have estimate := pair phase (firstFamily.canonicalExteriorStaticCoefficient firstIndex time)
    (finalFamily.canonicalExteriorStaticCoefficient finalIndex time) firstWeighted finalWeighted
    increment increment nearby nearby
  simp only [sub_self, norm_zero, mul_zero, zero_add] at estimate
  rw [firstSeries, finalSeries]
  exact ((operator.le_opNorm _).trans (mul_le_mul_of_nonneg_left estimate (norm_nonneg operator))).trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
