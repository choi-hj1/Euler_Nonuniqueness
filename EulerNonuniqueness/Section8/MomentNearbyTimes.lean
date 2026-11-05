import EulerNonuniqueness.Section8.MomentSampledVelocity
import EulerNonuniqueness.General.WeakLimitIdentification

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem MomentCompactnessData.exists_common_velocity_limit_at_nearby_times
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (indices : ℕ → ℕ) (firstTimes secondTimes : ℕ → Icc (0 : ℝ) horizon)
    (nearby : Tendsto (fun index => (secondTimes index : ℝ) - firstTimes index) atTop (𝓝 0)) :
    ∃ limit : Vorticity, InitialDatum limit ∧ ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      Tendsto (fun index => eLpNorm
        (biotSavart (sequence (indices (subsequence index)) (firstTimes (subsequence index))) -
          biotSavart limit) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun index => eLpNorm
        (biotSavart (sequence (indices (subsequence index)) (secondTimes (subsequence index))) -
          biotSavart limit) 2 volume) atTop (𝓝 0) := by
  let firstParameters : ℕ → ℕ × Icc (0 : ℝ) horizon := fun index => (indices index, firstTimes index)
  obtain ⟨firstLimit, firstDatum, firstExtraction, firstIncreasing, firstWeak, firstVelocity⟩ :=
    data.exists_joint_vorticity_velocity_subsequence firstParameters
  let secondParameters : ℕ → ℕ × Icc (0 : ℝ) horizon := fun index =>
    (indices (firstExtraction index), secondTimes (firstExtraction index))
  obtain ⟨secondLimit, secondDatum, secondExtraction, secondIncreasing, secondWeak, secondVelocity⟩ :=
    data.exists_joint_vorticity_velocity_subsequence secondParameters
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
    obtain ⟨bound, _, bounded⟩ := data.momentTimeBound test smooth compact
    have timeConverges := nearby.comp increasing.tendsto_atTop
    have boundConverges : Tendsto
        (fun index => bound * |(secondTimes (extraction index) : ℝ) - firstTimes (extraction index)|)
        atTop (𝓝 0) := by
      simpa only [mul_zero, abs_zero] using timeConverges.abs.const_mul bound
    apply squeeze_zero_norm (fun index => ?_) boundConverges
    change ‖(∫ position, sequence (indices (extraction index)) (firstTimes (extraction index)) position * test position) -
      (∫ position, sequence (indices (extraction index)) (secondTimes (extraction index)) position * test position)‖ ≤ _
    rw [norm_sub_rev, Real.norm_eq_abs]
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
  · simpa only [extraction, firstParameters, Function.comp_def] using firstVelocity.comp secondIncreasing.tendsto_atTop
  · rw [velocityEquality]
    simpa only [extraction, secondParameters, Function.comp_def] using secondVelocity

theorem MomentCompactnessData.tendsto_velocity_sub_at_nearby_times
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (indices : ℕ → ℕ) (firstTimes secondTimes : ℕ → Icc (0 : ℝ) horizon)
    (nearby : Tendsto (fun index => (secondTimes index : ℝ) - firstTimes index) atTop (𝓝 0)) :
    Tendsto (fun index => eLpNorm
      (biotSavart (sequence (indices index) (firstTimes index)) -
        biotSavart (sequence (indices index) (secondTimes index))) 2 volume) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro sampling samplingTends
  obtain ⟨limit, datum, extraction, _, firstConverges, secondConverges⟩ :=
    data.exists_common_velocity_limit_at_nearby_times
      (indices ∘ sampling) (firstTimes ∘ sampling) (secondTimes ∘ sampling) (nearby.comp samplingTends)
  refine ⟨extraction, ?_⟩
  have limitMember := datum.biotSavart_memLp_two
  have estimate (index : ℕ) : eLpNorm
      (biotSavart (sequence (indices (sampling (extraction index))) (firstTimes (sampling (extraction index)))) -
        biotSavart (sequence (indices (sampling (extraction index))) (secondTimes (sampling (extraction index))))) 2 volume ≤
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (firstTimes (sampling (extraction index)))) - biotSavart limit) 2 volume +
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (secondTimes (sampling (extraction index)))) - biotSavart limit) 2 volume := by
    have firstMember := data.biotSavart_memLp_two (indices (sampling (extraction index)))
      (firstTimes (sampling (extraction index))).property
    have secondMember := data.biotSavart_memLp_two (indices (sampling (extraction index)))
      (secondTimes (sampling (extraction index))).property
    have inequality := eLpNorm_sub_le (firstMember.sub limitMember).aestronglyMeasurable
      (secondMember.sub limitMember).aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa only [sub_sub_sub_cancel_right] using inequality
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun index =>
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (firstTimes (sampling (extraction index)))) - biotSavart limit) 2 volume +
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (secondTimes (sampling (extraction index)))) - biotSavart limit) 2 volume) atTop (𝓝 0) by
      simpa only [Function.comp_def, add_zero] using firstConverges.add secondConverges)
    (fun _ => zero_le _) estimate

end EulerNonuniqueness
