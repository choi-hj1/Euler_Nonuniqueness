import EulerNonuniqueness.Section8.TimeTransport
import EulerNonuniqueness.Section8.InitialVelocity
import EulerNonuniqueness.Section8.VelocityContinuity
import EulerNonuniqueness.Section8.UniformVelocityBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

structure MomentCompactnessData (horizon : ℝ) (sequence : ℕ → Evolution) : Prop where
  supported : ∃ radius : ℝ, 0 < radius ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
    Function.support (sequence index time) ⊆ Metric.closedBall 0 radius
  zeroMean : ∀ index, ∀ time ∈ Icc 0 horizon, (∫ position, sequence index time position) = 0
  members : ∀ exponent : ℝ, 1 ≤ exponent → ∀ index, ∀ time ∈ Icc 0 horizon,
    MemLp (sequence index time) (ENNReal.ofReal exponent) volume
  normBounded : ∀ exponent : ℝ, 1 ≤ exponent → ∃ bound : ℝ≥0∞, bound < (⊤ : ℝ≥0∞) ∧
    ∀ index, ∀ time ∈ Icc 0 horizon, eLpNorm (sequence index time) (ENNReal.ofReal exponent) volume ≤ bound
  momentTimeBound : ∀ test : Vorticity, ContDiff ℝ ∞ test → HasCompactSupport test →
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, ∀ first ∈ Icc 0 horizon, ∀ second ∈ Icc 0 horizon,
      |(∫ position, sequence index second position * test position) -
        (∫ position, sequence index first position * test position)| ≤ bound * |second - first|

theorem LocalCompactnessHypotheses.momentCompactnessData
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (positive : 0 < horizon) :
    MomentCompactnessData horizon sequence := by
  refine ⟨hypotheses.2.1, fun index time inside => ((hypotheses.2.2 index).2.2.1 time inside).2,
    fun exponent bound index time inside => ((hypotheses.2.2 index).2.2.2 exponent bound time inside).1,
    fun _ bound => hypotheses.uniform_eLpNorm_bound positive.le bound, ?_⟩
  intro test smooth compact
  exact hypotheses.uniform_smooth_moment_time_bound positive smooth compact

theorem MomentCompactnessData.datum {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (index : ℕ) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    InitialDatum (sequence index time) := by
  obtain ⟨radius, _, supported⟩ := data.supported
  exact ⟨HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 radius) (supported index time inside),
    fun exponent bound => data.members exponent bound index time inside, data.zeroMean index time inside⟩

theorem MomentCompactnessData.biotSavart_memLp_two {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (index : ℕ) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    MemLp (biotSavart (sequence index time)) 2 volume :=
  (data.datum index inside).biotSavart_memLp_two

theorem MomentCompactnessData.continuous_biotSavart {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (index : ℕ) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Continuous (biotSavart (sequence index time)) := by
  obtain ⟨radius, positive, supported⟩ := data.supported
  exact continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (data.members 4 (by norm_num) index time inside) (by norm_num) positive.le (supported index time inside)

theorem MomentCompactnessData.uniform_velocity_bound {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, ∀ time ∈ Icc 0 horizon, ∀ position,
      ‖biotSavart (sequence index time) position‖ ≤ bound := by
  obtain ⟨oneBound, oneFinite, oneBounded⟩ := data.normBounded 1 le_rfl
  obtain ⟨fourBound, fourFinite, fourBounded⟩ := data.normBounded 4 (by norm_num)
  let kernelNorm := (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
    (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal
  refine ⟨fourBound.toReal * kernelNorm + oneBound.toReal * (1 / (2 * Real.pi)), by dsimp [kernelNorm]; positivity, ?_⟩
  intro index time inside position
  have integrable : Integrable (sequence index time) :=
    memLp_one_iff_integrable.mp (by simpa only [ENNReal.ofReal_one] using data.members 1 le_rfl index time inside)
  have massBound : (∫ source, ‖sequence index time source‖) ≤ oneBound.toReal := by
    have estimate := ENNReal.toReal_mono oneFinite.ne (oneBounded index time inside)
    simpa only [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm integrable.aestronglyMeasurable] using estimate
  exact (norm_biotSavart_le_L1_L4 integrable (data.members 4 (by norm_num) index time inside) position).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (ENNReal.toReal_mono fourFinite.ne (fourBounded index time inside)) ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right massBound (by positivity)))

end EulerNonuniqueness
