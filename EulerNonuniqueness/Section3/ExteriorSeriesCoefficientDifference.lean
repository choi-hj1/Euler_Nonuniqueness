import EulerNonuniqueness.Section3.ExteriorPowerSeriesBounds

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

theorem summable_exterior_coefficient_difference_weight (initial final : ℕ → ℂ)
    {weight : ℝ} (nonnegative : 0 ≤ weight)
    (initialSummable : Summable (fun degree => weight ^ (degree + 1) * ‖initial degree‖))
    (finalSummable : Summable (fun degree => weight ^ (degree + 1) * ‖final degree‖)) :
    Summable (fun degree => weight ^ (degree + 1) * ‖initial degree - final degree‖) := by
  apply Summable.of_nonneg_of_le (fun degree => by positivity) _ (initialSummable.add finalSummable)
  intro degree
  have bound := mul_le_mul_of_nonneg_left (norm_sub_le (initial degree) (final degree))
    (pow_nonneg nonnegative (degree + 1))
  simpa only [mul_add] using bound

theorem rotatedExteriorPower_sub_coefficient (phase : Circle) (data : PeriodicC1HolderHalf)
    (degree : ℕ) (initial final : ℂ) :
    rotatedExteriorPower phase data degree initial - rotatedExteriorPower phase data degree final =
      rotatedExteriorPower phase data degree (initial - final) := by
  simp only [rotatedExteriorPower, mul_sub, sub_smul]

theorem rotatedExteriorPowerFirstJet_sub_coefficient (phase : Circle) (data : PeriodicC1HolderHalf)
    (degree : ℕ) (initial final : ℂ) :
    rotatedExteriorPowerFirstJet phase data degree initial - rotatedExteriorPowerFirstJet phase data degree final =
      rotatedExteriorPowerFirstJet phase data degree (initial - final) := by
  apply ContinuousLinearMap.ext
  intro direction
  simp only [ContinuousLinearMap.sub_apply, rotatedExteriorPowerFirstJet_apply, mul_sub, sub_smul]

theorem exteriorContourPowerSeries_sub_coefficient (phase : Circle) (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (initial final : ℕ → ℂ)
    (initialSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖initial degree‖))
    (finalSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖final degree‖)) :
    exteriorContourPowerSeries phase initial data - exteriorContourPowerSeries phase final data =
      exteriorContourPowerSeries phase (fun degree => initial degree - final degree) data := by
  unfold exteriorContourPowerSeries
  rw [← tsum_sub (rotatedExteriorPower_summable phase data bound initial initialSummable)
    (rotatedExteriorPower_summable phase data bound final finalSummable)]
  congr 1
  funext degree
  exact rotatedExteriorPower_sub_coefficient phase data degree _ _

theorem exteriorContourPowerSeriesFirstJet_sub_coefficient (phase : Circle) (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (initial final : ℕ → ℂ)
    (initialSummable : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * ‖initial degree‖))
    (finalSummable : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * ‖final degree‖)) :
    exteriorContourPowerSeriesFirstJet phase initial data - exteriorContourPowerSeriesFirstJet phase final data =
      exteriorContourPowerSeriesFirstJet phase (fun degree => initial degree - final degree) data := by
  unfold exteriorContourPowerSeriesFirstJet
  rw [← tsum_sub (exteriorContourPowerSeriesFirstJet_summable phase initial data bound initialSummable)
    (exteriorContourPowerSeriesFirstJet_summable phase final data bound finalSummable)]
  congr 1
  funext degree
  exact rotatedExteriorPowerFirstJet_sub_coefficient phase data degree _ _

theorem exteriorContourPowerSeries_coefficient_difference_norm_le (phase : Circle) (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (initial final : ℕ → ℂ)
    (initialSummable : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖initial degree‖))
    (finalSummable : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖final degree‖)) :
    ‖exteriorContourPowerSeries phase initial data - exteriorContourPowerSeries phase final data‖ ≤
      ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initial degree - final degree‖ := by
  rw [exteriorContourPowerSeries_sub_coefficient phase data bound initial final
    (summable_exteriorCoefficientWeight_mono initial (by norm_num) (by norm_num) initialSummable)
    (summable_exteriorCoefficientWeight_mono final (by norm_num) (by norm_num) finalSummable)]
  exact exteriorContourPowerSeries_norm_bound phase _ data bound
    (summable_exterior_coefficient_difference_weight initial final (by norm_num) initialSummable finalSummable)

theorem exteriorContourPowerSeriesFirstJet_coefficient_difference_norm_le (phase : Circle) (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (initial final : ℕ → ℂ)
    (initialSummable : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖initial degree‖))
    (finalSummable : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖final degree‖)) :
    ‖exteriorContourPowerSeriesFirstJet phase initial data - exteriorContourPowerSeriesFirstJet phase final data‖ ≤
      ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initial degree - final degree‖ := by
  rw [exteriorContourPowerSeriesFirstJet_sub_coefficient phase data bound initial final
    (summable_exteriorCoefficientWeight_mono initial (by norm_num) (by norm_num) initialSummable)
    (summable_exteriorCoefficientWeight_mono final (by norm_num) (by norm_num) finalSummable)]
  exact exteriorContourPowerSeriesFirstJet_norm_bound96 phase _ data bound
    (summable_exterior_coefficient_difference_weight initial final (by norm_num) initialSummable finalSummable)

end EulerNonuniqueness.Paper
