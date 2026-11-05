import EulerNonuniqueness.Section3.ProjectedExteriorSeriesTaylor

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

def exteriorCoefficientWithoutLeading (coefficient : ℕ → ℂ) (power : ℕ) : ℂ :=
  if power = 0 then 0 else coefficient power

theorem exteriorCoefficientWithoutLeading_weight_summable (coefficient : ℕ → ℂ) {weight : ℝ}
    (nonnegative : 0 ≤ weight)
    (summable : Summable (fun power => weight ^ (power + 1) * ‖coefficient power‖)) :
    Summable (fun power => weight ^ (power + 1) * ‖exteriorCoefficientWithoutLeading coefficient power‖) := by
  apply Summable.of_nonneg_of_le (fun power => by positivity) (fun power => ?_) summable
  by_cases zero : power = 0
  · simp only [exteriorCoefficientWithoutLeading, if_pos zero, norm_zero, mul_zero]
    positivity
  · simp only [exteriorCoefficientWithoutLeading, if_neg zero]
    exact le_rfl

theorem c1NaturalPower_one (data : PeriodicC1HolderHalf) : c1NaturalPower data 1 = data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [c1NaturalPower_value, pow_one]

theorem exteriorContourPowerSeries_without_leading (phase : Circle) (coefficient : ℕ → ℂ)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (weighted : Summable (fun power => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    exteriorContourPowerSeries phase (exteriorCoefficientWithoutLeading coefficient) data =
      exteriorContourPowerSeries phase coefficient data -
        (((phase : ℂ)⁻¹ ^ 2 * coefficient 0) • c1Conjugate data) := by
  have fullSum := (rotatedExteriorPower_summable phase data bound coefficient weighted).hasSum
  have singleSum := hasSum_ite_eq (0 : ℕ) (rotatedExteriorPower phase data 0 (coefficient 0))
  have tailSum : HasSum (fun power => rotatedExteriorPower phase data power
      (exteriorCoefficientWithoutLeading coefficient power))
      (exteriorContourPowerSeries phase coefficient data - rotatedExteriorPower phase data 0 (coefficient 0)) := by
    convert fullSum.sub singleSum using 1
    funext power
    by_cases zero : power = 0
    · subst power
      simp only [exteriorCoefficientWithoutLeading, ite_true, rotatedExteriorPower, mul_zero, zero_smul, sub_self]
    · simp only [exteriorCoefficientWithoutLeading, if_neg zero, sub_zero]
  have identity := tailSum.tsum_eq
  have leading : rotatedExteriorPower phase data 0 (coefficient 0) =
      ((phase : ℂ)⁻¹ ^ 2 * coefficient 0) • c1Conjugate data := by
    change ((phase : ℂ)⁻¹ ^ 2 * coefficient 0) • c1Conjugate (c1NaturalPower data 1) = _
    rw [c1NaturalPower_one]
  rw [leading] at identity
  exact identity

theorem circleBasedProjectedExteriorSeries_without_leading (phase : Circle) (coefficient : ℕ → ℂ)
    (base : PeriodicC1HolderHalf) (bound : ‖standardCircleBanach + base‖ ≤ 3)
    (weighted : Summable (fun power => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    circleBasedProjectedExteriorSeries phase (exteriorCoefficientWithoutLeading coefficient) base =
      circleBasedProjectedExteriorSeries phase coefficient base -
        contourCentroidGaugeProjection (standardCircleBanach + base)
          (((phase : ℂ)⁻¹ ^ 2 * coefficient 0) • c1Conjugate (standardCircleBanach + base)) := by
  unfold circleBasedProjectedExteriorSeries circleBasedCentroidProjection
  rw [exteriorContourPowerSeries_without_leading phase coefficient _ bound weighted, map_sub]

end EulerNonuniqueness.Paper
