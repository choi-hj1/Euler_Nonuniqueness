import EulerNonuniqueness.Section3.CanonicalProjectedExteriorSeries
import EulerNonuniqueness.Section3.ExteriorCoefficientUniformWeights
import EulerNonuniqueness.Section3.ContourGaugeOperatorUniform

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_uniform_value_bound :
    ∃ radius > 0, radius ≤ 1 / 12 ∧ ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
        (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 48 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle) (increment : PeriodicC1HolderHalf), ‖increment‖ ≤ radius →
      ‖family.canonicalProjectedExteriorContourField index time distance positive
        (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment)‖ ≤ constant * weight := by
  obtain ⟨gaugeRadius, gaugePositive, _, gaugeConstant, gaugeOne, gaugeBounds, _, _⟩ :=
    circleBasedCentroidProjection_exists_uniform_firstJet_bounds
  let radius := min (gaugeRadius / 2) (1 / 12)
  let constant := 24 * gaugeConstant / Real.pi + 1
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have radiusGauge : radius ≤ gaugeRadius := (min_le_left _ _).trans (by linarith)
  have radiusSmall : radius ≤ 1 / 12 := min_le_right _ _
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 24 * gaugeConstant / Real.pi := by positivity
    dsimp [constant]
    linarith
  refine ⟨radius, radiusPositive, radiusSmall, constant, constantOne, ?_⟩
  intro count family index time distance weight positive weightNonnegative small separated weightBound phase increment inside
  let coefficient := fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (power + 1) time
  have nearby : ‖increment‖ < 1 / 3 := lt_of_le_of_lt (inside.trans radiusSmall) (by norm_num)
  have dataBound : ‖standardCircleBanach + increment‖ ≤ 3 := by
    have triangle := norm_add_le standardCircleBanach increment
    linarith [standardCircleBanach_norm_bound]
  have ratio : 24 * (family.patch index).radius / distance < 1 := (div_lt_one positive).mpr
    (by linarith [(family.patch index).radius_positive])
  have coefficientIdentity (power : ℕ) : coefficient power = exteriorVorticityCoefficient
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time)
      (family.patch index).radius power := family.exteriorTaylorCoefficient_eq_vorticityCoefficient
        (Finset.univ.erase index) (family.patch index).center (family.patch index).radius time power positive separated
  have supportGap := family.subfamily_support_separated (Finset.univ.erase index)
    ((family.patch index).center time) time distance separated
  have weighted : Summable (fun power => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖) := by
    simp_rw [coefficientIdentity]
    exact summable_exteriorVorticityCoefficient_weight
      (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) _
      (family.patch index).radius_positive.le positive (by norm_num) supportGap ratio
  have sumBound : (∑' power, (24 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤ 24 * weight / Real.pi := by
    simp_rw [coefficientIdentity]
    exact tsum_exteriorVorticityCoefficient_weight_le_uniform
      (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) _
      (family.patch index).radius_positive.le positive (by norm_num) weightNonnegative supportGap
      (by norm_num; exact small) weightBound
  have seriesBound : ‖exteriorContourPowerSeries phase coefficient (standardCircleBanach + increment)‖ ≤
      24 * weight / Real.pi := by
    have actual := (rotatedExteriorPower_summable phase (standardCircleBanach + increment) dataBound coefficient weighted).hasSum.norm_le_of_bounded
      weighted.hasSum (fun power => rotatedExteriorPower_norm_bound phase (standardCircleBanach + increment) dataBound power _)
    exact actual.trans sumBound
  have gaugeBound : ‖contourCentroidGaugeProjection (standardCircleBanach + increment)‖ ≤ gaugeConstant := by
    simpa only [circleBasedCentroidProjection] using (gaugeBounds increment (inside.trans radiusGauge)).1
  rw [family.canonicalProjectedExteriorContourField_eq_series index time distance positive
    (by linarith [(family.patch index).radius_positive]) separated phase increment nearby ratio]
  change ‖contourCentroidGaugeProjection (standardCircleBanach + increment)
    (exteriorContourPowerSeries phase coefficient (standardCircleBanach + increment))‖ ≤ constant * weight
  calc
    _ ≤ ‖contourCentroidGaugeProjection (standardCircleBanach + increment)‖ *
        ‖exteriorContourPowerSeries phase coefficient (standardCircleBanach + increment)‖ :=
      (contourCentroidGaugeProjection _).le_opNorm _
    _ ≤ gaugeConstant * (24 * weight / Real.pi) :=
      mul_le_mul gaugeBound seriesBound (norm_nonneg _) (by linarith)
    _ ≤ constant * weight := by
      have difference := mul_le_mul_of_nonneg_right (show 24 * gaugeConstant / Real.pi ≤ constant by dsimp [constant]; linarith) weightNonnegative
      convert difference using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
