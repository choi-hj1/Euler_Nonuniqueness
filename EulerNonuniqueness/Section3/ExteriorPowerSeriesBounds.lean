import EulerNonuniqueness.Section3.ExteriorPowerSeriesFirstJet

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

theorem exteriorContourPowerSeries_norm_bound (phase : Circle) (coefficient : ℕ → ℂ)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (weighted : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    ‖exteriorContourPowerSeries phase coefficient data‖ ≤
      ∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖ := by
  have weighted24 := summable_exteriorCoefficientWeight_mono coefficient
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) weighted
  apply (rotatedExteriorPower_summable phase data bound coefficient weighted24).hasSum.norm_le_of_bounded weighted.hasSum
  intro power
  exact (rotatedExteriorPower_norm_bound phase data bound power _).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 24)
      (by norm_num : (24 : ℝ) ≤ 96) _) (norm_nonneg _))

theorem exteriorContourPowerSeriesFirstJet_norm_bound96 (phase : Circle) (coefficient : ℕ → ℂ)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (weighted : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    ‖exteriorContourPowerSeriesFirstJet phase coefficient data‖ ≤
      ∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖ := by
  have weighted48 := summable_exteriorCoefficientWeight_mono coefficient
    (by norm_num : (0 : ℝ) ≤ 48) (by norm_num : (48 : ℝ) ≤ 96) weighted
  apply (exteriorContourPowerSeriesFirstJet_summable phase coefficient data bound weighted48).hasSum.norm_le_of_bounded weighted.hasSum
  intro power
  exact (rotatedExteriorPowerFirstJet_norm_bound phase data bound power _).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 48)
      (by norm_num : (48 : ℝ) ≤ 96) _) (norm_nonneg _))

theorem exteriorContourPowerSeries_difference_bound (phase : Circle) (coefficient : ℕ → ℂ)
    (first base : PeriodicC1HolderHalf) (firstBound : ‖first‖ ≤ 3) (baseBound : ‖base‖ ≤ 3)
    (small : ‖first - base‖ ≤ 1)
    (weighted : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    ‖exteriorContourPowerSeries phase coefficient first - exteriorContourPowerSeries phase coefficient base‖ ≤
      2 * (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) * ‖first - base‖ := by
  have amplitudeNonnegative : 0 ≤ ∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖ :=
    tsum_nonneg (fun power => by positivity)
  have errorBound := exteriorContourPowerSeriesFirstJet_error_bound phase coefficient first base firstBound baseBound weighted
  have derivativeBound := (exteriorContourPowerSeriesFirstJet phase coefficient base).le_opNorm (first - base)
  have operatorBound := exteriorContourPowerSeriesFirstJet_norm_bound96 phase coefficient base baseBound weighted
  have triangle := norm_add_le
    (exteriorContourPowerSeries phase coefficient first - exteriorContourPowerSeries phase coefficient base -
      exteriorContourPowerSeriesFirstJet phase coefficient base (first - base))
    (exteriorContourPowerSeriesFirstJet phase coefficient base (first - base))
  rw [sub_add_cancel] at triangle
  have combined := triangle.trans (add_le_add errorBound
    (derivativeBound.trans (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg _))))
  have squareBound : ‖first - base‖ ^ 2 ≤ ‖first - base‖ := by
    nlinarith [norm_nonneg (first - base)]
  nlinarith [mul_le_mul_of_nonneg_left squareBound amplitudeNonnegative]

end EulerNonuniqueness.Paper
