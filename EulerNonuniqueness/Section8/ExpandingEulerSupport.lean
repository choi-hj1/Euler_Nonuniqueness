import EulerNonuniqueness.Section8.ExpandingEulerSequence
import EulerNonuniqueness.Section8.RegularizedLimitSupport
import EulerNonuniqueness.General.SupportedLpSeries

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem expanding_euler_limit_support_and_zeroMean
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (solutions : ∀ index : ℕ, IsEulerSolutionOn (index + 1) initial (sequence index))
    (zeroMean : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1), ∫ position, sequence index time position = 0)
    {radius speed : ℝ}
    (supported : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1),
      support (sequence index time) ⊆ Metric.closedBall 0 (radius + speed * time))
    {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence) {limit : Evolution}
    (limitSolution : IsEulerSolution initial limit)
    (convergence : ∀ stage : ℕ, UniformLpConvergenceOn (stage + 1) 1 (sequence ∘ subsequence) limit)
    {time : ℝ} (nonnegative : 0 ≤ time) :
    limit time =ᵐ[volume] growingSupportMask radius speed limit time ∧
      (∫ position, limit time position) = 0 := by
  let cutoff := Nat.ceil time
  have above (index : ℕ) : time ≤ ((subsequence (index + cutoff) : ℕ) : ℝ) + 1 := by
    have ceiling : time ≤ (cutoff : ℝ) := Nat.le_ceil time
    have lower := increasing.id_le (index + cutoff)
    have lowerReal : (index : ℝ) + cutoff ≤ (subsequence (index + cutoff) : ℝ) := by exact_mod_cast lower
    linarith [Nat.cast_nonneg (α := ℝ) index]
  have sequenceIntegrable (index : ℕ) : Integrable (sequence (subsequence (index + cutoff)) time) :=
    memLp_one_iff_integrable.mp (by simpa using
      (solutions (subsequence (index + cutoff))).memLp (exponent := 1) le_rfl ⟨nonnegative, above index⟩)
  have normConvergence : Tendsto
      (fun index => eLpNorm (sequence (subsequence (index + cutoff)) time - limit time) 1 volume) atTop (𝓝 0) :=
    ((convergence cutoff).tendsto_eLpNorm ⟨nonnegative, (Nat.le_ceil time).trans (by linarith)⟩).comp
      (tendsto_add_atTop_nat cutoff)
  have limitIntegrable := limitSolution.integrable time nonnegative
  refine ⟨ae_eq_indicator_of_tendsto_eLpNorm_sub_of_support (by norm_num)
    (fun index => (sequenceIntegrable index).aestronglyMeasurable) limitIntegrable.aestronglyMeasurable
    (fun index => supported (subsequence (index + cutoff)) time ⟨nonnegative, above index⟩) normConvergence, ?_⟩
  have integralConvergence := tendsto_integral_of_L1' (limit time) limitIntegrable
    (Eventually.of_forall sequenceIntegrable) normConvergence
  have sequenceMeanZero (index : ℕ) : (∫ position, sequence (subsequence (index + cutoff)) time position) = 0 :=
    zeroMean (subsequence (index + cutoff)) time ⟨nonnegative, above index⟩
  exact tendsto_nhds_unique (by simpa only [sequenceMeanZero] using integralConvergence) tendsto_const_nhds

theorem aestronglyMeasurable_growingSupportMask
    {horizon radius speed : ℝ} {omega : Evolution}
    (measurable : AEStronglyMeasurable (Function.uncurry omega) (spacetimeMeasure horizon)) :
    AEStronglyMeasurable (Function.uncurry (growingSupportMask radius speed omega)) (spacetimeMeasure horizon) := by
  have regionMeasurable : MeasurableSet
      {point : ℝ × Plane | ‖point.2‖ ≤ radius + speed * point.1} :=
    (isClosed_le continuous_snd.norm (continuous_const.add (continuous_const.mul continuous_fst))).measurableSet
  convert measurable.indicator regionMeasurable using 1
  funext point
  by_cases inside : ‖point.2‖ ≤ radius + speed * point.1
  · simp [Function.uncurry, growingSupportMask, indicator_apply, Metric.mem_closedBall, dist_zero_right, inside]
  · simp [Function.uncurry, growingSupportMask, indicator_apply, Metric.mem_closedBall, dist_zero_right, inside]

theorem exists_growing_support_global_euler_of_expanding_solutions
    {initial : Vorticity} {sequence : ℕ → Evolution} (datum : InitialDatum initial)
    (solutions : ∀ index : ℕ, IsEulerSolutionOn (index + 1) initial (sequence index))
    (zeroMean : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1), ∫ position, sequence index time position = 0)
    {radius speed : ℝ} (radiusPositive : 0 < radius) (speedNonnegative : 0 ≤ speed)
    (supported : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1),
      support (sequence index time) ⊆ Metric.closedBall 0 (radius + speed * time)) :
    ∃ omega : Evolution, IsEulerSolution initial omega ∧
      (∀ horizon : ℝ, AEStronglyMeasurable (Function.uncurry omega) (spacetimeMeasure horizon)) ∧
      (∀ time : ℝ, 0 ≤ time → support (omega time) ⊆ Metric.closedBall 0 (radius + speed * time)) ∧
      ∀ time : ℝ, 0 ≤ time → InitialDatum (omega time) := by
  have hypotheses := tailCompactness_of_expanding_euler_solutions datum solutions zeroMean
    radiusPositive speedNonnegative supported
  obtain ⟨subsequence, localLimit, limit, increasing, localSolutions, equality,
    vorticityConvergence, _, measurable⟩ := exists_tail_global_limit_local_ae hypotheses
  have horizonBound (horizon : ℝ) : horizon ≤ (Nat.ceil horizon : ℝ) + 1 :=
    (Nat.le_ceil horizon).trans (by linarith)
  have localSolution (horizon : ℝ) (positive : 0 < horizon) : IsEulerSolutionOn horizon initial limit := by
    apply ((localSolutions (Nat.ceil horizon)).mono (horizonBound horizon)).congr_ae positive.le (measurable horizon)
    intro time inside
    exact equality (Nat.ceil horizon) time ⟨inside.1, inside.2.trans (horizonBound horizon)⟩
  have globalSolution := isEulerSolution_of_isEulerSolutionOn localSolution
  have limitProperties (time : ℝ) (nonnegative : 0 ≤ time) :=
    expanding_euler_limit_support_and_zeroMean solutions zeroMean supported increasing globalSolution
      (fun stage => by simpa using vorticityConvergence stage 1 le_rfl) nonnegative
  let omega := growingSupportMask radius speed limit
  have maskedMeasurable (horizon : ℝ) : AEStronglyMeasurable (Function.uncurry omega) (spacetimeMeasure horizon) :=
    aestronglyMeasurable_growingSupportMask (measurable horizon)
  have maskedLocal (horizon : ℝ) (positive : 0 < horizon) : IsEulerSolutionOn horizon initial omega :=
    (localSolution horizon positive).congr_ae positive.le (maskedMeasurable horizon)
      (fun time inside => (limitProperties time inside.1).1)
  have maskedGlobal := isEulerSolution_of_isEulerSolutionOn maskedLocal
  refine ⟨omega, maskedGlobal, maskedMeasurable,
    fun time _ => support_growingSupportMask_subset radius speed limit time, ?_⟩
  intro time nonnegative
  refine ⟨HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (radius + speed * time))
    (support_growingSupportMask_subset radius speed limit time), ?_, ?_⟩
  · intro exponent exponentBound
    obtain ⟨_, membership, _⟩ := maskedGlobal.2.1 exponent exponentBound
    exact membership ⟨time, nonnegative⟩
  · exact (integral_congr_ae (limitProperties time nonnegative).1.symm).trans (limitProperties time nonnegative).2

end EulerNonuniqueness
