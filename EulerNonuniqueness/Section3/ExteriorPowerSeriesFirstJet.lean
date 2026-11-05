import EulerNonuniqueness.Section3.ExteriorPowerFirstJet

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

local instance exteriorPowerSeriesOperatorSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem summable_exteriorCoefficientWeight_mono (coefficient : ℕ → ℂ)
    {lower upper : ℝ} (nonnegative : 0 ≤ lower) (ordered : lower ≤ upper)
    (summable : Summable (fun power => upper ^ (power + 1) * ‖coefficient power‖)) :
    Summable (fun power => lower ^ (power + 1) * ‖coefficient power‖) :=
  Summable.of_nonneg_of_le (fun power => by positivity)
    (fun power => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ nonnegative ordered _) (norm_nonneg _)) summable

def exteriorContourPowerSeries (phase : Circle) (coefficient : ℕ → ℂ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf := ∑' power, rotatedExteriorPower phase data power (coefficient power)

def exteriorContourPowerSeriesFirstJet (phase : Circle) (coefficient : ℕ → ℂ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  ∑' power, rotatedExteriorPowerFirstJet phase data power (coefficient power)

theorem exteriorContourPowerSeriesFirstJet_summable (phase : Circle) (coefficient : ℕ → ℂ)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (weighted : Summable (fun power => (48 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    Summable (fun power => rotatedExteriorPowerFirstJet phase data power (coefficient power)) :=
  Summable.of_norm_bounded _ weighted (fun power => rotatedExteriorPowerFirstJet_norm_bound phase data bound power _)

theorem exteriorContourPowerSeriesFirstJet_norm_bound (phase : Circle) (coefficient : ℕ → ℂ)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (weighted : Summable (fun power => (48 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    ‖exteriorContourPowerSeriesFirstJet phase coefficient data‖ ≤
      ∑' power, (48 : ℝ) ^ (power + 1) * ‖coefficient power‖ :=
  (exteriorContourPowerSeriesFirstJet_summable phase coefficient data bound weighted).hasSum.norm_le_of_bounded
    weighted.hasSum (fun power => rotatedExteriorPowerFirstJet_norm_bound phase data bound power _)

theorem exteriorContourPowerSeriesFirstJet_error_bound (phase : Circle) (coefficient : ℕ → ℂ)
    (first base : PeriodicC1HolderHalf) (firstBound : ‖first‖ ≤ 3) (baseBound : ‖base‖ ≤ 3)
    (weighted : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    ‖exteriorContourPowerSeries phase coefficient first - exteriorContourPowerSeries phase coefficient base -
      exteriorContourPowerSeriesFirstJet phase coefficient base (first - base)‖ ≤
      (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) * ‖first - base‖ ^ 2 := by
  have weighted24 := summable_exteriorCoefficientWeight_mono coefficient
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) weighted
  have weighted48 := summable_exteriorCoefficientWeight_mono coefficient
    (by norm_num : (0 : ℝ) ≤ 48) (by norm_num : (48 : ℝ) ≤ 96) weighted
  have firstSum := (rotatedExteriorPower_summable phase first firstBound coefficient weighted24).hasSum
  have baseSum := (rotatedExteriorPower_summable phase base baseBound coefficient weighted24).hasSum
  have operatorSum := exteriorContourPowerSeriesFirstJet_summable phase coefficient base baseBound weighted48
  have appliedSum := (ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf (first - base)).hasSum operatorSum.hasSum
  have errorSum := (firstSum.sub baseSum).sub appliedSum
  exact errorSum.norm_le_of_bounded (weighted.hasSum.mul_right (‖first - base‖ ^ 2))
    (fun power => rotatedExteriorPowerFirstJet_error_bound phase first base firstBound baseBound power _)

theorem hasFDerivAt_exteriorContourPowerSeries (phase : Circle) (coefficient : ℕ → ℂ)
    (base : PeriodicC1HolderHalf) (bound : ‖base‖ < 3)
    (weighted : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    HasFDerivAt (exteriorContourPowerSeries phase coefficient)
      (exteriorContourPowerSeriesFirstJet phase coefficient base) base := by
  apply EulerNonuniqueness.General.hasFDerivAt_of_eventual_quadratic_remainder
    (exteriorContourPowerSeries phase coefficient) (exteriorContourPowerSeriesFirstJet phase coefficient base) base
    (constant := ∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)
    (tsum_nonneg (fun power => by positivity))
  have nearby : ∀ᶠ increment : PeriodicC1HolderHalf in 𝓝 0, ‖base + increment‖ < 3 := by
    have continuity : Continuous (fun increment : PeriodicC1HolderHalf => ‖base + increment‖) :=
      (continuous_const.add continuous_id).norm
    exact (continuity.tendsto 0).eventually (eventually_lt_nhds (by simpa only [add_zero] using bound))
  filter_upwards [nearby] with increment small
  simpa only [add_sub_cancel_left] using
    exteriorContourPowerSeriesFirstJet_error_bound phase coefficient (base + increment) base small.le bound.le weighted

end EulerNonuniqueness.Paper
