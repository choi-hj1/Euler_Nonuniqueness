import EulerNonuniqueness.Section3.CanonicalProjectedExteriorSeries
import EulerNonuniqueness.Section3.ExteriorSeriesLeadingMode
import EulerNonuniqueness.Section3.ExteriorCoefficientUniformWeights

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_higher_mode_linear_bound :
    ∃ radius > 0, radius ≤ 1 / 12 ∧ ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
        (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle),
      let leading := (phase : ℂ)⁻¹ ^ 2 * family.exteriorTaylorCoefficient (Finset.univ.erase index)
        (family.patch index).center (family.patch index).radius 1 time
      let field := fun increment : PeriodicC1HolderHalf =>
        family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment) -
        contourCentroidGaugeProjection (standardCircleBanach + increment)
          (leading • c1Conjugate (standardCircleBanach + increment))
      ∀ base : PeriodicC1HolderHalf, ‖base‖ ≤ radius →
        DifferentiableAt ℝ field base ∧
          ‖fderiv ℝ field base‖ ≤ constant * weight * ((family.patch index).radius / distance) := by
  obtain ⟨seriesRadius, seriesPositive, seriesSmall, seriesConstant, seriesConstantOne, seriesBounds⟩ :=
    circleBasedProjectedExteriorSeries_exists_uniform_firstJet
  let constant := 2 * (96 : ℝ) ^ 2 * seriesConstant / Real.pi + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 2 * (96 : ℝ) ^ 2 * seriesConstant / Real.pi := by positivity
    dsimp [constant]
    linarith
  refine ⟨seriesRadius / 2, by positivity, by linarith, constant, constantOne, ?_⟩
  intro count family index time distance weight positive weightNonnegative small separated weightBound phase
  let coefficient := fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (power + 1) time
  let tail := exteriorCoefficientWithoutLeading coefficient
  let field := fun increment : PeriodicC1HolderHalf =>
    family.canonicalProjectedExteriorContourField index time distance positive
      (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment) -
    contourCentroidGaugeProjection (standardCircleBanach + increment)
      (((phase : ℂ)⁻¹ ^ 2 * coefficient 0) • c1Conjugate (standardCircleBanach + increment))
  have integrable := family.subfamilyVorticity_integrable (Finset.univ.erase index) time
  have supportGap := family.subfamily_support_separated (Finset.univ.erase index)
    ((family.patch index).center time) time distance separated
  have coefficientIdentity (power : ℕ) : coefficient power =
      exteriorVorticityCoefficient (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) (family.patch index).radius power :=
    family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius time power positive separated
  have ratio96 : 96 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have ratio24 : 24 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have weighted : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) := by
    simp_rw [coefficientIdentity]
    exact summable_exteriorVorticityCoefficient_weight integrable _ (family.patch index).radius_positive.le
      positive (by norm_num) supportGap ratio96
  have weighted24 := summable_exteriorCoefficientWeight_mono coefficient
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) weighted
  have tailWeighted := exteriorCoefficientWithoutLeading_weight_summable coefficient (by norm_num : (0 : ℝ) ≤ 96) weighted
  have tailIdentity (power : ℕ) : tail power =
      exteriorHigherVorticityCoefficient (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) (family.patch index).radius power := by
    unfold tail exteriorCoefficientWithoutLeading exteriorHigherVorticityCoefficient
    split_ifs
    · rfl
    · exact coefficientIdentity power
  have tailSumBound : (∑' power, (96 : ℝ) ^ (power + 1) * ‖tail power‖) ≤
      2 * (96 : ℝ) ^ 2 * (family.patch index).radius * weight / (Real.pi * distance) := by
    simp_rw [tailIdentity]
    exact tsum_exteriorHigherVorticityCoefficient_weight_le integrable _ (family.patch index).radius_positive.le
      positive (by norm_num) weightNonnegative supportGap (by linarith) weightBound
  have identity (base : PeriodicC1HolderHalf) (nearby : ‖base‖ < 1 / 3) :
      field base = circleBasedProjectedExteriorSeries phase tail base := by
    have shapeBound : ‖standardCircleBanach + base‖ ≤ 3 := by
      have triangle := norm_add_le standardCircleBanach base
      linarith [standardCircleBanach_norm_bound]
    unfold field
    rw [family.canonicalProjectedExteriorContourField_eq_series index time distance positive _ separated phase base nearby ratio24]
    exact (circleBasedProjectedExteriorSeries_without_leading phase coefficient base shapeBound weighted24).symm
  change ∀ base : PeriodicC1HolderHalf, ‖base‖ ≤ seriesRadius / 2 →
    DifferentiableAt ℝ field base ∧
      ‖fderiv ℝ field base‖ ≤ constant * weight * ((family.patch index).radius / distance)
  intro base baseBound
  have sourceJet := (seriesBounds phase tail tailWeighted).2.2 base (by linarith)
  have nearby : ∀ᶠ current : PeriodicC1HolderHalf in 𝓝 base, ‖current‖ < 1 / 3 :=
    (continuous_norm.tendsto base).eventually (eventually_lt_nhds (by linarith : ‖base‖ < 1 / 3))
  have equality : field =ᶠ[𝓝 base] circleBasedProjectedExteriorSeries phase tail := by
    filter_upwards [nearby] with current close
    exact identity current close
  have actualJet := sourceJet.congr_of_eventuallyEq equality
  refine ⟨actualJet.differentiableAt, ?_⟩
  rw [actualJet.fderiv]
  refine ((seriesBounds phase tail tailWeighted).1 base (by linarith)).trans ?_
  refine (mul_le_mul_of_nonneg_left tailSumBound (by linarith : 0 ≤ seriesConstant)).trans ?_
  calc
    _ = (2 * (96 : ℝ) ^ 2 * seriesConstant / Real.pi) * weight * ((family.patch index).radius / distance) := by ring
    _ ≤ constant * weight * ((family.patch index).radius / distance) := by
      apply mul_le_mul_of_nonneg_right _
        (div_nonneg (family.patch index).radius_positive.le positive.le)
      apply mul_le_mul_of_nonneg_right _ weightNonnegative
      dsimp [constant]
      linarith

end EulerNonuniqueness.Paper
