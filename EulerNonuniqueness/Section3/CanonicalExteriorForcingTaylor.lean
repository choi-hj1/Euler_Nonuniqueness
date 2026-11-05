import EulerNonuniqueness.Section3.CanonicalProjectedExteriorSeries
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

theorem canonicalProjectedExteriorContourField_exists_uniform_Taylor :
    ∃ radius > 0, radius ≤ 1 / 12 ∧ ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
        (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle),
      let field := fun increment : PeriodicC1HolderHalf =>
        family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment)
      (∀ base : PeriodicC1HolderHalf, ‖base‖ ≤ radius →
        DifferentiableAt ℝ field base ∧ ‖fderiv ℝ field base‖ ≤ constant * weight) ∧
      ∀ base increment : PeriodicC1HolderHalf, ‖base‖ + ‖increment‖ ≤ radius →
        ‖field (base + increment) - field base - fderiv ℝ field base increment‖ ≤
          constant * weight * ‖increment‖ ^ 2 := by
  obtain ⟨seriesRadius, seriesPositive, seriesSmall, seriesConstant, seriesConstantOne, seriesBounds⟩ :=
    circleBasedProjectedExteriorSeries_exists_uniform_firstJet
  let constant := 96 * seriesConstant / Real.pi + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 96 * seriesConstant / Real.pi := by positivity
    dsimp [constant]
    linarith
  refine ⟨seriesRadius / 2, by positivity, by linarith, constant, constantOne, ?_⟩
  intro count family index time distance weight positive weightNonnegative small separated weightBound phase
  let field := fun increment : PeriodicC1HolderHalf =>
    family.canonicalProjectedExteriorContourField index time distance positive
      (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment)
  let coefficient := fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (power + 1) time
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
  have sumBound : (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤ 96 * weight / Real.pi := by
    simp_rw [coefficientIdentity]
    exact tsum_exteriorVorticityCoefficient_weight_le_uniform integrable _ (family.patch index).radius_positive.le
      positive (by norm_num) weightNonnegative supportGap (by linarith) weightBound
  have amplitudeBound : seriesConstant * (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤ constant * weight := by
    refine (mul_le_mul_of_nonneg_left sumBound (by linarith : 0 ≤ seriesConstant)).trans ?_
    calc
      _ = (96 * seriesConstant / Real.pi) * weight := by ring
      _ ≤ constant * weight := by dsimp [constant]; nlinarith
  have identity (base : PeriodicC1HolderHalf) (nearby : ‖base‖ < 1 / 3) :
      field base = circleBasedProjectedExteriorSeries phase coefficient base :=
    family.canonicalProjectedExteriorContourField_eq_series index time distance positive _ separated phase base nearby ratio24
  have jet (base : PeriodicC1HolderHalf) (baseBound : ‖base‖ ≤ seriesRadius / 2) :
      HasFDerivAt field (circleBasedProjectedExteriorSeriesFirstJet phase coefficient base) base := by
    have sourceJet := (seriesBounds phase coefficient weighted).2.2 base (by linarith)
    have nearby : ∀ᶠ current : PeriodicC1HolderHalf in 𝓝 base, ‖current‖ < 1 / 3 :=
      (continuous_norm.tendsto base).eventually (eventually_lt_nhds (by linarith : ‖base‖ < 1 / 3))
    have equality : field =ᶠ[𝓝 base] circleBasedProjectedExteriorSeries phase coefficient := by
      filter_upwards [nearby] with current close
      exact identity current close
    exact sourceJet.congr_of_eventuallyEq equality
  refine ⟨?_, ?_⟩
  · intro base baseBound
    refine ⟨(jet base baseBound).differentiableAt, ?_⟩
    rw [(jet base baseBound).fderiv]
    exact ((seriesBounds phase coefficient weighted).1 base (by linarith)).trans amplitudeBound
  · intro base increment inside
    change ‖field (base + increment) - field base - fderiv ℝ field base increment‖ ≤
      constant * weight * ‖increment‖ ^ 2
    have baseBound : ‖base‖ ≤ seriesRadius / 2 := by linarith [norm_nonneg increment]
    have finalBound : ‖base + increment‖ ≤ seriesRadius / 2 := (norm_add_le _ _).trans inside
    rw [identity (base + increment) (by linarith), identity base (by linarith), (jet base baseBound).fderiv]
    exact ((seriesBounds phase coefficient weighted).2.1 base increment (by linarith)).trans
      (mul_le_mul_of_nonneg_right amplitudeBound (sq_nonneg _))

end EulerNonuniqueness.Paper
