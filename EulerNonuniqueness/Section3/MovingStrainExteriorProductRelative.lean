import EulerNonuniqueness.Section3.MovingStrainCorrectionPairBounds
import EulerNonuniqueness.Section3.ProjectedExteriorSeriesPairBounds

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  powerFirstJetOperatorGroup exteriorPowerSeriesOperatorSpace gaugeOperatorUniformSecondGroup

theorem movingStrainExteriorProduct_exists_scaled_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ (phase : Circle) (initialCoefficient finalCoefficient : ℕ → ℂ),
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) →
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖) →
      ∀ firstBase finalBase firstData finalData : PeriodicC1HolderHalf,
      ‖firstBase - standardCircleBanach‖ ≤ radius → ‖finalBase - standardCircleBanach‖ ≤ radius →
      ‖firstData‖ ≤ radius → ‖finalData‖ ≤ radius →
      ∀ initialStrain finalStrain : ℂ, ∀ frequency : ℝ,
      ‖frequency⁻¹ • (movingStrainRealCorrectionCLM firstBase initialStrain
          (circleBasedProjectedExteriorSeries phase initialCoefficient firstData)) -
        frequency⁻¹ • (movingStrainRealCorrectionCLM finalBase finalStrain
          (circleBasedProjectedExteriorSeries phase finalCoefficient finalData))‖ ≤
      constant / |frequency| *
        (‖initialStrain‖ *
          (((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) +
              (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) * ‖firstData - finalData‖ +
            ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖) +
          (‖initialStrain‖ * ‖firstBase - finalBase‖ + ‖initialStrain - finalStrain‖) *
            (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) := by
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionNonnegative, correction⟩ :=
    movingStrainRealCorrectionCLM_exists_pair_apply_bounds
  obtain ⟨sourceRadius, sourcePositive, _, sourceConstant, sourceNonnegative, sourceAbsolute, sourceDifference⟩ :=
    circleBasedProjectedExteriorSeries_exists_pair_value_bounds
  refine ⟨min correctionRadius sourceRadius, lt_min correctionPositive sourcePositive,
    correctionConstant * sourceConstant, mul_nonneg correctionNonnegative sourceNonnegative, ?_⟩
  intro phase initialCoefficient finalCoefficient initialSummable finalSummable firstBase finalBase firstData finalData
    firstBaseInside finalBaseInside firstInside finalInside initialStrain finalStrain frequency
  have forceDifference := sourceDifference phase initialCoefficient finalCoefficient initialSummable finalSummable
    firstData finalData (firstInside.trans (min_le_right _ _)) (finalInside.trans (min_le_right _ _))
  have forceAbsolute := sourceAbsolute phase finalCoefficient finalSummable finalData
    (finalInside.trans (min_le_right _ _))
  have product := correction firstBase finalBase
    (firstBaseInside.trans (min_le_left _ _)) (finalBaseInside.trans (min_le_left _ _))
    initialStrain finalStrain
    (circleBasedProjectedExteriorSeries phase initialCoefficient firstData)
    (circleBasedProjectedExteriorSeries phase finalCoefficient finalData)
  have bounded :
      ‖movingStrainRealCorrectionCLM firstBase initialStrain
          (circleBasedProjectedExteriorSeries phase initialCoefficient firstData) -
        movingStrainRealCorrectionCLM finalBase finalStrain
          (circleBasedProjectedExteriorSeries phase finalCoefficient finalData)‖ ≤
      (correctionConstant * sourceConstant) *
        (‖initialStrain‖ *
          (((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) +
              (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) * ‖firstData - finalData‖ +
            ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖) +
          (‖initialStrain‖ * ‖firstBase - finalBase‖ + ‖initialStrain - finalStrain‖) *
            (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) := by
    apply product.trans
    calc
      _ ≤ correctionConstant *
        (‖initialStrain‖ *
          (sourceConstant * (((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) +
              (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) * ‖firstData - finalData‖ +
            ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖)) +
          (‖initialStrain‖ * ‖firstBase - finalBase‖ + ‖initialStrain - finalStrain‖) *
            (sourceConstant * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖))) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left forceDifference (norm_nonneg initialStrain))
          (mul_le_mul_of_nonneg_left forceAbsolute (by positivity))) correctionNonnegative
      _ = _ := by ring
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv]
  exact (mul_le_mul_of_nonneg_left bounded (inv_nonneg.mpr (abs_nonneg frequency))).trans_eq (by
    simp only [div_eq_mul_inv]
    ring)

end EulerNonuniqueness.Paper
