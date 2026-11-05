import EulerNonuniqueness.Section3.RelabeledPrimitiveSeriesDifference
import EulerNonuniqueness.Section3.ExteriorSeriesCoefficientDifference

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance primitiveCoefficientDifferenceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem relabeledDiskForcingPrimitive_sub_amplitude (angular : PeriodicC1HolderHalf) (degree : ℕ)
    (frequency : ℝ) (initial final : ℝ → ℂ) (time : ℝ) :
    relabeledDiskForcingPrimitive angular degree frequency initial time -
      relabeledDiskForcingPrimitive angular degree frequency final time =
      relabeledDiskForcingPrimitive angular degree frequency (fun current => initial current - final current) time := by
  simp only [relabeledDiskForcingPrimitive, mul_sub, sub_mul, sub_smul]

theorem relabeledForcingPrimitiveSeries_sub_amplitude (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (initial final : ℕ → ℝ → ℂ) (time : ℝ)
    (initialSummable : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖initial degree time‖))
    (finalSummable : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖final degree time‖)) :
    relabeledForcingPrimitiveSeries angular frequency initial time -
      relabeledForcingPrimitiveSeries angular frequency final time =
      relabeledForcingPrimitiveSeries angular frequency (fun degree current => initial degree current - final degree current) time := by
  have firstSeries : Summable (fun degree => relabeledDiskForcingPrimitive angular degree frequency (initial degree) time) :=
    Summable.of_norm_bounded _ (initialSummable.mul_left (32 / |frequency|))
      (fun degree => relabeledDiskForcingPrimitive_weighted_bound angular small realValues degree nonzero _ time)
  have finalSeries : Summable (fun degree => relabeledDiskForcingPrimitive angular degree frequency (final degree) time) :=
    Summable.of_norm_bounded _ (finalSummable.mul_left (32 / |frequency|))
      (fun degree => relabeledDiskForcingPrimitive_weighted_bound angular small realValues degree nonzero _ time)
  unfold relabeledForcingPrimitiveSeries
  rw [← firstSeries.tsum_sub finalSeries]
  congr 1
  funext degree
  exact relabeledDiskForcingPrimitive_sub_amplitude angular degree frequency _ _ time

theorem relabeledForcingPrimitiveSeries_amplitude_difference_norm_le (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (initial final : ℕ → ℝ → ℂ) (time : ℝ)
    (initialSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖initial degree time‖))
    (finalSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖final degree time‖)) :
    ‖relabeledForcingPrimitiveSeries angular frequency initial time -
      relabeledForcingPrimitiveSeries angular frequency final time‖ ≤
      (32 / |frequency|) * ∑' degree, (24 : ℝ) ^ (degree + 1) * ‖initial degree time - final degree time‖ := by
  have firstTwo := summable_exteriorCoefficientWeight_mono (fun degree => initial degree time)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 24) initialSummable
  have finalTwo := summable_exteriorCoefficientWeight_mono (fun degree => final degree time)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 24) finalSummable
  have difference24 := summable_exterior_coefficient_difference_weight
    (fun degree => initial degree time) (fun degree => final degree time) (by norm_num : (0 : ℝ) ≤ 24)
    initialSummable finalSummable
  have differenceTwo := summable_exteriorCoefficientWeight_mono
    (fun degree => initial degree time - final degree time)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 24) difference24
  rw [relabeledForcingPrimitiveSeries_sub_amplitude angular small realValues nonzero initial final time firstTwo finalTwo]
  have estimate := relabeledForcingPrimitiveSeries_norm_bound angular small realValues nonzero
    (fun degree current => initial degree current - final degree current) time differenceTwo
  have sums := Summable.tsum_le_tsum
    (fun degree => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 24) _) (norm_nonneg _))
    differenceTwo difference24
  exact estimate.trans (mul_le_mul_of_nonneg_left sums (by positivity))

theorem relabeledForcingPrimitiveSeries_pair_difference_norm_le
    (firstAngular finalAngular : PeriodicC1HolderHalf)
    (firstSmall : ‖firstAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2)
    (firstReal : ∀ label, star (firstAngular.val.1 label) = firstAngular.val.1 label)
    (finalReal : ∀ label, star (finalAngular.val.1 label) = finalAngular.val.1 label)
    (firstBound : ‖diskRelabelCurve firstAngular 1‖ ≤ 3)
    (finalBound : ‖diskRelabelCurve finalAngular 1‖ ≤ 3)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (initial final : ℕ → ℝ → ℂ) (time : ℝ)
    (initialSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖initial degree time‖))
    (finalSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖final degree time‖)) :
    ‖relabeledForcingPrimitiveSeries firstAngular frequency initial time -
      relabeledForcingPrimitiveSeries finalAngular frequency final time‖ ≤
      (2 / |frequency|) * (∑' degree, (24 : ℝ) ^ (degree + 1) * ‖initial degree time‖) *
        ‖diskRelabelCurve firstAngular 1 - diskRelabelCurve finalAngular 1‖ +
      (32 / |frequency|) * ∑' degree, (24 : ℝ) ^ (degree + 1) * ‖initial degree time - final degree time‖ := by
  have angular := relabeledForcingPrimitiveSeries_difference_bound firstAngular finalAngular firstSmall finalSmall
    firstReal finalReal firstBound finalBound nonzero initial time initialSummable
  have coefficient := relabeledForcingPrimitiveSeries_amplitude_difference_norm_le finalAngular finalSmall finalReal
    nonzero initial final time initialSummable finalSummable
  exact (norm_sub_le_norm_sub_add_norm_sub
    (relabeledForcingPrimitiveSeries firstAngular frequency initial time)
    (relabeledForcingPrimitiveSeries finalAngular frequency initial time)
    (relabeledForcingPrimitiveSeries finalAngular frequency final time)).trans (add_le_add angular coefficient)

end EulerNonuniqueness.Paper
