import EulerNonuniqueness.General.WeakLimitIdentification
import EulerNonuniqueness.Section8.SampledVelocityCompactness
import EulerNonuniqueness.Section8.TimeTransport

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.exists_common_velocity_limit_at_nearby_times
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) (indices : ℕ → ℕ)
    (firstTimes secondTimes : ℕ → Icc (0 : ℝ) horizon)
    (nearby : Tendsto (fun index => (secondTimes index : ℝ) - firstTimes index) atTop (𝓝 0)) :
    ∃ limit : Vorticity, InitialDatum limit ∧ ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      Tendsto (fun index => eLpNorm
        (biotSavart (sequence (indices (subsequence index)) (firstTimes (subsequence index))) -
          biotSavart limit) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun index => eLpNorm
        (biotSavart (sequence (indices (subsequence index)) (secondTimes (subsequence index))) -
          biotSavart limit) 2 volume) atTop (𝓝 0) := by
  let firstParameters : ℕ → ℕ × Icc (0 : ℝ) horizon := fun index => (indices index, firstTimes index)
  obtain ⟨firstLimit, firstDatum, firstExtraction, firstIncreasing, firstWeak, firstVelocity⟩ :=
    hypotheses.exists_joint_vorticity_velocity_subsequence horizonPositive.le firstParameters
  let secondParameters : ℕ → ℕ × Icc (0 : ℝ) horizon := fun index =>
    (indices (firstExtraction index), secondTimes (firstExtraction index))
  obtain ⟨secondLimit, secondDatum, secondExtraction, secondIncreasing, secondWeak, secondVelocity⟩ :=
    hypotheses.exists_joint_vorticity_velocity_subsequence horizonPositive.le secondParameters
  let extraction := firstExtraction ∘ secondExtraction
  have increasing : StrictMono extraction := firstIncreasing.comp secondIncreasing
  let first : ℕ → Vorticity := fun index => sequence (indices (extraction index)) (firstTimes (extraction index))
  let second : ℕ → Vorticity := fun index => sequence (indices (extraction index)) (secondTimes (extraction index))
  have firstWeakConverges (test : Vorticity) (testMember : MemLp test 2 volume) :
      Tendsto (fun index => ∫ position, first index position * test position) atTop
        (𝓝 (∫ position, firstLimit position * test position)) := by
    simpa only [first, extraction, firstParameters, Function.comp_def] using
      (firstWeak test testMember).comp secondIncreasing.tendsto_atTop
  have secondWeakConverges (test : Vorticity) (testMember : MemLp test 2 volume) :
      Tendsto (fun index => ∫ position, second index position * test position) atTop
        (𝓝 (∫ position, secondLimit position * test position)) := by
    simpa only [second, extraction, secondParameters, Function.comp_def] using secondWeak test testMember
  have momentsClose (test : Vorticity) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
      Tendsto (fun index => (∫ position, first index position * test position) -
        (∫ position, second index position * test position)) atTop (𝓝 0) := by
    obtain ⟨bound, boundNonnegative, bounded⟩ :=
      hypotheses.uniform_smooth_moment_time_bound horizonPositive smooth compact
    have timeConverges := nearby.comp increasing.tendsto_atTop
    have boundConverges : Tendsto
        (fun index => bound * |(secondTimes (extraction index) : ℝ) - firstTimes (extraction index)|)
        atTop (𝓝 0) := by
      simpa only [mul_zero, abs_zero] using timeConverges.abs.const_mul bound
    apply squeeze_zero_norm (fun index => ?_) boundConverges
    change ‖(∫ position, sequence (indices (extraction index)) (firstTimes (extraction index)) position * test position) -
      (∫ position, sequence (indices (extraction index)) (secondTimes (extraction index)) position * test position)‖ ≤ _
    rw [norm_sub_rev]
    exact bounded (indices (extraction index)) (firstTimes (extraction index)) (firstTimes (extraction index)).property
      (secondTimes (extraction index)) (secondTimes (extraction index)).property
  have firstMember : MemLp firstLimit 2 volume := by simpa using firstDatum.2.1 2 (by norm_num)
  have secondMember : MemLp secondLimit 2 volume := by simpa using secondDatum.2.1 2 (by norm_num)
  have equalAlmostEverywhere : firstLimit =ᵐ[volume] secondLimit :=
    ae_eq_of_weakL2_limits_of_smooth_pairing_sub_tendsto_zero firstMember secondMember
      firstWeakConverges secondWeakConverges momentsClose
  have velocityEquality : biotSavart firstLimit = biotSavart secondLimit := by
    funext position
    apply integral_congr_ae
    filter_upwards [equalAlmostEverywhere] with source equality
    rw [equality]
  refine ⟨firstLimit, firstDatum, extraction, increasing, ?_, ?_⟩
  · simpa only [extraction, firstParameters, Function.comp_def] using
      firstVelocity.comp secondIncreasing.tendsto_atTop
  · rw [velocityEquality]
    simpa only [extraction, secondParameters, Function.comp_def] using secondVelocity

end EulerNonuniqueness
