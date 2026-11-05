import EulerNonuniqueness.Section8.CompactnessStatement
import EulerNonuniqueness.General.DiagonalSubsequence
import EulerNonuniqueness.Section8.Restriction

/-!
# Diagonal extraction on increasing time intervals

These results implement the subsequence operations used after Lemma 8.1.
-/

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology
open scoped ContDiff

namespace EulerNonuniqueness

theorem WeakTransportOn.locallyIntegrableOn {horizon : ℝ} {initial : Vorticity}
    {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity) :
    LocallyIntegrableOn (Function.uncurry omega) (Ioo 0 horizon ×ˢ univ)
      ((volume : Measure ℝ).prod (volume : Measure Plane)) := by
  intro center inside
  have openDomain : IsOpen (Ioo (0 : ℝ) horizon ×ˢ (univ : Set Plane)) :=
    isOpen_Ioo.prod isOpen_univ
  obtain ⟨radius, positive, ballSubset⟩ := Metric.mem_nhds_iff.mp (openDomain.mem_nhds inside)
  let bump : ContDiffBump center := ⟨radius / 2, radius, half_pos positive,
    half_lt_self positive⟩
  let test : ℝ × Plane → ℝ := fun point => point.1 * bump point
  have testAdmissible : ScalarTestOn horizon test := by
    refine ⟨contDiff_fst.mul bump.contDiff, bump.hasCompactSupport.mul_left, ?_⟩
    intro time position afterHorizon
    have outside : radius ≤ dist (time, position) center := by
      by_contra before
      have inDomain := ballSubset (show (time, position) ∈ Metric.ball center radius from
        lt_of_not_ge before)
      exact (not_lt_of_ge afterHorizon) inDomain.1.2
    simp only [test, bump.zero_of_le_dist outside, mul_zero]
  let integrand := fun point : ℝ × Plane => omega point.1 point.2 *
    (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))
  have integrable : Integrable integrand (spacetimeMeasure horizon) :=
    (transport test testAdmissible).1
  have smallerSubset : Metric.ball center (radius / 2) ⊆ Ioo 0 horizon ×ˢ univ :=
    (Metric.ball_subset_ball (half_le_self positive.le)).trans ballSubset
  have integrableOnBall : IntegrableOn integrand (Metric.ball center (radius / 2))
      ((volume : Measure ℝ).prod (volume : Measure Plane)) := by
    have restricted := integrable.restrict (s := Metric.ball center (radius / 2))
    simpa only [spacetimeMeasure, Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_restrict_of_subset smallerSubset] using restricted
  refine ⟨Metric.ball center (radius / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds center (half_pos positive)), ?_⟩
  apply integrableOnBall.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with point inBall
  have equalNear : test =ᶠ[𝓝 point] Prod.fst := by
    filter_upwards [bump.eventuallyEq_one_of_mem_ball inBall] with nearby equal
    simp only [test, equal, Pi.one_apply, mul_one]
  simp only [integrand, timeDerivative, spatialDerivative, equalNear.fderiv_eq,
    fderiv_fst, Function.uncurry]
  change omega point.1 point.2 * (1 + 0) = omega point.1 point.2
  ring

theorem WeakTransportOn.aestronglyMeasurable {horizon : ℝ} {initial : Vorticity}
    {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity) :
    AEStronglyMeasurable (Function.uncurry omega) (spacetimeMeasure horizon) := by
  simpa only [spacetimeMeasure, Measure.restrict_prod_eq_prod_univ] using
    transport.locallyIntegrableOn.aestronglyMeasurable

theorem InitialLpConvergence.subsequence {sequence : ℕ → Evolution}
    {initial : Vorticity} (convergence : InitialLpConvergence sequence initial)
    {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence) :
    InitialLpConvergence (sequence ∘ subsequence) initial := by
  refine ⟨convergence.1, ?_⟩
  intro exponent exponentBound
  exact (convergence.2 exponent exponentBound).comp increasing.tendsto_atTop

theorem LocalCompactnessHypotheses.subsequence {horizon : ℝ} {initial : Vorticity}
    {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence) :
    LocalCompactnessHypotheses horizon initial (sequence ∘ subsequence) := by
  refine ⟨hypotheses.1.subsequence increasing, ?_, fun index => hypotheses.2.2 (subsequence index)⟩
  obtain ⟨radius, positive, supported⟩ := hypotheses.2.1
  exact ⟨radius, positive, fun index => supported (subsequence index)⟩

theorem GlobalCompactnessHypotheses.subsequence {initial : Vorticity}
    {sequence : ℕ → Evolution}
    (hypotheses : GlobalCompactnessHypotheses initial sequence)
    {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence) :
    GlobalCompactnessHypotheses initial (sequence ∘ subsequence) := by
  intro horizon positive
  exact (hypotheses horizon positive).subsequence increasing

theorem UniformLpConvergenceOn.subsequence {Value : Type*} [NormedAddCommGroup Value]
    {horizon : ℝ} {exponent : ℝ≥0∞} {sequence : ℕ → ℝ → Plane → Value}
    {limit : ℝ → Plane → Value}
    (convergence : UniformLpConvergenceOn horizon exponent sequence limit)
    {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence) :
    UniformLpConvergenceOn horizon exponent (sequence ∘ subsequence) limit := by
  intro tolerance positive
  obtain ⟨cutoff, afterCutoff⟩ := convergence tolerance positive
  exact ⟨cutoff, fun index large =>
    afterCutoff (subsequence index) (large.trans (increasing.id_le index))⟩

theorem UniformLpConvergenceOn.mono {Value : Type*} [NormedAddCommGroup Value]
    {horizon smaller : ℝ} {exponent : ℝ≥0∞} {sequence : ℕ → ℝ → Plane → Value}
    {limit : ℝ → Plane → Value}
    (convergence : UniformLpConvergenceOn horizon exponent sequence limit)
    (ordered : smaller ≤ horizon) :
    UniformLpConvergenceOn smaller exponent sequence limit := by
  intro tolerance positive
  obtain ⟨cutoff, afterCutoff⟩ := convergence tolerance positive
  exact ⟨cutoff, fun index large time inside =>
    afterCutoff index large time ⟨inside.1, inside.2.trans ordered⟩⟩

theorem UniformLpConvergenceOn.diagonal {Value : Type*} [NormedAddCommGroup Value]
    {horizon : ℝ} {exponent : ℝ≥0∞} {sequence : ℕ → ℝ → Plane → Value}
    {limit : ℝ → Plane → Value} {extractions : ℕ → ℕ → ℕ}
    (increasing : ∀ stage, StrictMono (extractions stage)) (stage : ℕ)
    (convergence : UniformLpConvergenceOn horizon exponent
      (sequence ∘ Nat.nestedExtraction extractions stage) limit) :
    UniformLpConvergenceOn horizon exponent
      (fun index => sequence (Nat.nestedExtraction extractions index index)) limit := by
  intro tolerance positive
  obtain ⟨cutoff, afterCutoff⟩ := convergence tolerance positive
  apply eventually_atTop.mp
  exact Nat.eventually_nestedExtraction_diagonal increasing stage
    (property := fun index => ∀ time ∈ Icc 0 horizon,
      eLpNorm (sequence index time - limit time) exponent volume < ENNReal.ofReal tolerance)
    (eventually_atTop.mpr ⟨cutoff, afterCutoff⟩)

theorem UniformLpConvergenceOn.tendsto_eLpNorm {Value : Type*}
    [NormedAddCommGroup Value] {horizon : ℝ} {exponent : ℝ≥0∞}
    {sequence : ℕ → ℝ → Plane → Value} {limit : ℝ → Plane → Value}
    (convergence : UniformLpConvergenceOn horizon exponent sequence limit)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Tendsto (fun index => eLpNorm (sequence index time - limit time) exponent volume)
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro tolerance positive
  by_cases finite : tolerance = ⊤
  · simp only [finite, le_top, Filter.eventually_true]
  · obtain ⟨cutoff, afterCutoff⟩ := convergence tolerance.toReal
      (ENNReal.toReal_pos positive.ne' finite)
    refine eventually_atTop.mpr ⟨cutoff, fun index large => ?_⟩
    simpa only [ENNReal.ofReal_toReal finite] using (afterCutoff index large time inside).le

theorem UniformLpConvergenceOn.ae_eq {Value : Type*} [NormedAddCommGroup Value]
    {horizon : ℝ} {exponent : ℝ≥0∞} {sequence : ℕ → ℝ → Plane → Value}
    {first second : ℝ → Plane → Value}
    (exponentBound : 1 ≤ exponent)
    (firstConvergence : UniformLpConvergenceOn horizon exponent sequence first)
    (secondConvergence : UniformLpConvergenceOn horizon exponent sequence second)
    {time : ℝ} (inside : time ∈ Icc 0 horizon)
    (sequenceMeasurable : ∀ index, AEStronglyMeasurable (sequence index time) volume)
    (firstMeasurable : AEStronglyMeasurable (first time) volume)
    (secondMeasurable : AEStronglyMeasurable (second time) volume) :
    first time =ᵐ[volume] second time := by
  have bounds : ∀ index, eLpNorm (first time - second time) exponent volume ≤
      eLpNorm (sequence index time - first time) exponent volume +
        eLpNorm (sequence index time - second time) exponent volume := by
    intro index
    have difference : first time - second time =
        (sequence index time - second time) - (sequence index time - first time) := by
      funext position
      simp only [Pi.sub_apply]
      abel
    rw [difference, add_comm]
    exact eLpNorm_sub_le ((sequenceMeasurable index).sub secondMeasurable)
      ((sequenceMeasurable index).sub firstMeasurable) exponentBound
  have convergence := (firstConvergence.tendsto_eLpNorm inside).add
    (secondConvergence.tendsto_eLpNorm inside)
  have zero : eLpNorm (first time - second time) exponent volume = 0 := by
    apply le_antisymm _ bot_le
    simpa only [add_zero] using ge_of_tendsto convergence (Eventually.of_forall bounds)
  have differenceZero := (eLpNorm_eq_zero_iff (firstMeasurable.sub secondMeasurable)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one exponentBound))).mp zero
  filter_upwards [differenceZero] with position equal
  exact sub_eq_zero.mp equal

theorem biotSavart_congr_ae {first second : Vorticity} (equal : first =ᵐ[volume] second) :
    biotSavart first = biotSavart second := by
  funext position
  exact integral_congr_ae (equal.mono (fun source sourceEqual =>
    congrArg (fun value => value • biotSavartKernel (position - source)) sourceEqual))

theorem BiotSavartIntegrable.congr_ae {first second : Vorticity}
    (integrability : BiotSavartIntegrable first) (equal : first =ᵐ[volume] second) :
    BiotSavartIntegrable second := by
  filter_upwards [integrability] with position integrable
  apply integrable.congr
  exact equal.mono (fun source sourceEqual =>
    congrArg (fun value => value • biotSavartKernel (position - source)) sourceEqual)

theorem UniformLpConvergenceOn.tendsto_l1Distance {horizon : ℝ}
    {sequence : ℕ → Evolution} {limit : Evolution}
    (convergence : UniformLpConvergenceOn horizon 1 sequence limit)
    {time : ℝ} (inside : time ∈ Icc 0 horizon)
    (sequenceMeasurable : ∀ index, AEStronglyMeasurable (sequence index time) volume)
    (limitMeasurable : AEStronglyMeasurable (limit time) volume) :
    Tendsto (fun index => l1Distance (sequence index time) (limit time)) atTop (𝓝 0) := by
  have normConvergence := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
    (convergence.tendsto_eLpNorm inside)
  have integralEqual : ∀ index,
      l1Distance (sequence index time) (limit time) =
        (eLpNorm (sequence index time - limit time) 1 volume).toReal := by
    intro index
    simpa only [l1Distance, Real.norm_eq_abs, Pi.sub_apply, eLpNorm_one_eq_lintegral_enorm]
      using integral_norm_eq_lintegral_enorm ((sequenceMeasurable index).sub limitMeasurable)
  simpa only [integralEqual, ENNReal.toReal_zero] using normConvergence

theorem IsEulerSolutionOn.memLp {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (solution : IsEulerSolutionOn horizon initial omega) {exponent : ℝ}
    (exponentBound : 1 ≤ exponent) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    MemLp (omega time) (ENNReal.ofReal exponent) volume := by
  obtain ⟨bound, membership, continuity⟩ := solution.2.1 exponent exponentBound
  exact membership ⟨time, inside⟩

theorem UniformLpConvergenceOn.congr_limit {Value : Type*} [NormedAddCommGroup Value]
    {horizon : ℝ} {exponent : ℝ≥0∞} {sequence : ℕ → ℝ → Plane → Value}
    {first second : ℝ → Plane → Value}
    (convergence : UniformLpConvergenceOn horizon exponent sequence first)
    (equal : ∀ time ∈ Icc 0 horizon, first time =ᵐ[volume] second time) :
    UniformLpConvergenceOn horizon exponent sequence second := by
  intro tolerance positive
  obtain ⟨cutoff, afterCutoff⟩ := convergence tolerance positive
  refine ⟨cutoff, fun index large time inside => ?_⟩
  have differenceEqual : sequence index time - first time =ᵐ[volume]
      sequence index time - second time :=
    Filter.EventuallyEq.sub Filter.EventuallyEq.rfl (equal time inside)
  exact (eLpNorm_congr_ae differenceEqual).symm.trans_lt
    (afterCutoff index large time inside)

theorem ContinuousInLpOn.congr_ae {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    {horizon : ℝ} {exponent : ℝ≥0∞} {first second : ℝ → Plane → Value}
    (continuity : ContinuousInLpOn horizon exponent first)
    (equal : ∀ time ∈ Icc 0 horizon, first time =ᵐ[volume] second time) :
    ContinuousInLpOn horizon exponent second := by
  obtain ⟨bound, membership, continuous⟩ := continuity
  letI : Fact (1 ≤ exponent) := ⟨bound⟩
  let secondMembership : ∀ time : Icc 0 horizon, MemLp (second time) exponent volume :=
    fun time => (memLp_congr_ae (equal time time.property)).mp (membership time)
  refine ⟨bound, secondMembership, ?_⟩
  apply continuous.congr
  intro time
  exact (membership time).toLp_congr (secondMembership time) (equal time time.property)

theorem continuousInLp_of_continuousInLpOn {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    {exponent : ℝ≥0∞} {field : ℝ → Plane → Value}
    (localContinuity : ∀ horizon : ℝ, 0 < horizon → ContinuousInLpOn horizon exponent field) :
    ContinuousInLp exponent field := by
  have exponentBound : 1 ≤ exponent := (localContinuity 1 zero_lt_one).1
  letI : Fact (1 ≤ exponent) := ⟨exponentBound⟩
  have member : ∀ time : ℝ≥0, MemLp (field time) exponent volume := by
    intro time
    obtain ⟨bound, membership, continuous⟩ := localContinuity (time + 1) (by positivity)
    exact membership ⟨time, time.property, by linarith⟩
  refine ⟨exponentBound, member, continuous_iff_continuousAt.mpr ?_⟩
  intro time
  obtain ⟨bound, membership, continuous⟩ := localContinuity (time + 1) (by positivity)
  let truncated : ℝ≥0 → Icc (0 : ℝ) (time + 1) := fun other =>
    ⟨min (other : ℝ) (time + 1), le_min other.property (by positivity), min_le_right _ _⟩
  have truncatedContinuous : Continuous truncated :=
    (continuous_subtype_val.min continuous_const).subtype_mk _
  have near : ∀ᶠ other : ℝ≥0 in 𝓝 time, (other : ℝ) < time + 1 :=
    (continuous_subtype_val : Continuous (fun other : ℝ≥0 => (other : ℝ))).continuousAt.eventually
      (gt_mem_nhds (lt_add_one (time : ℝ)))
  have agreement : (fun other : ℝ≥0 => (membership (truncated other)).toLp
      (field (truncated other))) =ᶠ[𝓝 time]
      (fun other : ℝ≥0 => (member other).toLp (field other)) := by
    filter_upwards [near] with other below
    apply MemLp.toLp_congr
    have truncatedEqual : ((truncated other : Icc (0 : ℝ) (time + 1)) : ℝ) = other :=
      min_eq_left below.le
    rw [truncatedEqual]
  exact ((continuous.comp truncatedContinuous).continuousAt).congr_of_eventuallyEq agreement.symm

set_option maxHeartbeats 800000 in
theorem exists_diagonal_local_limits (compactness : Lemma81Statement)
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : GlobalCompactnessHypotheses initial sequence) :
    ∃ subsequence : ℕ → ℕ, ∃ localLimit : ℕ → Evolution,
      StrictMono subsequence ∧ ∀ stage : ℕ,
        IsEulerSolutionOn (stage + 1) initial (localLimit stage) ∧
        (∀ exponent : ℝ, 1 ≤ exponent → UniformLpConvergenceOn (stage + 1)
          (ENNReal.ofReal exponent) (sequence ∘ subsequence) (localLimit stage)) ∧
        UniformLpConvergenceOn (stage + 1) 2
          (fun index time => biotSavart (sequence (subsequence index) time))
          (fun time => biotSavart (localLimit stage time)) := by
  let IncreasingSequence := {subsequence : ℕ → ℕ // StrictMono subsequence}
  have extract : ∀ stage : ℕ, ∀ previous : IncreasingSequence,
      ∃ next : ℕ → ℕ, ∃ limit : Evolution, StrictMono next ∧
        IsEulerSolutionOn (stage + 1) initial limit ∧
        (∀ exponent : ℝ, 1 ≤ exponent → UniformLpConvergenceOn (stage + 1)
          (ENNReal.ofReal exponent) ((sequence ∘ previous.val) ∘ next) limit) ∧
        UniformLpConvergenceOn (stage + 1) 2
          (fun index time => biotSavart (sequence (previous.val (next index)) time))
          (fun time => biotSavart (limit time)) := by
    intro stage previous
    exact compactness (stage + 1) (by positivity) initial (sequence ∘ previous.val)
      ((hypotheses.subsequence previous.property) (stage + 1) (by positivity))
  choose next localLimit nextIncreasing localSolution vorticityConvergence velocityConvergence
    using extract
  let stages : ℕ → IncreasingSequence := Nat.rec ⟨id, strictMono_id⟩
    (fun stage previous =>
      ⟨previous.val ∘ next stage previous, previous.property.comp (nextIncreasing stage previous)⟩)
  let extractions : ℕ → ℕ → ℕ := fun stage => next stage (stages stage)
  have extractionsIncreasing : ∀ stage, StrictMono (extractions stage) :=
    fun stage => nextIncreasing stage (stages stage)
  have stagesEqual : ∀ stage, (stages stage).val = Nat.nestedExtraction extractions stage := by
    intro stage
    induction stage with
    | zero => rfl
    | succ stage induction =>
      change (stages stage).val ∘ extractions stage =
        Nat.nestedExtraction extractions stage ∘ extractions stage
      rw [induction]
  let diagonal := fun index => Nat.nestedExtraction extractions index index
  refine ⟨diagonal, fun stage => localLimit stage (stages stage),
    Nat.strictMono_nestedExtraction_diagonal extractionsIncreasing, ?_⟩
  intro stage
  refine ⟨localSolution stage (stages stage), ?_, ?_⟩
  · intro exponent exponentBound
    have convergence := vorticityConvergence stage (stages stage) exponent exponentBound
    have rewritten : UniformLpConvergenceOn (stage + 1) (ENNReal.ofReal exponent)
        (sequence ∘ Nat.nestedExtraction extractions (stage + 1))
        (localLimit stage (stages stage)) := by
      simpa only [Nat.nestedExtraction, ← stagesEqual, Function.comp_assoc, extractions] using
        convergence
    exact UniformLpConvergenceOn.diagonal (sequence := sequence)
      (limit := localLimit stage (stages stage)) extractionsIncreasing (stage + 1) rewritten
  · have convergence := velocityConvergence stage (stages stage)
    have rewritten : UniformLpConvergenceOn (stage + 1) 2
        ((fun index time => biotSavart (sequence index time)) ∘
          Nat.nestedExtraction extractions (stage + 1))
        (fun time => biotSavart (localLimit stage (stages stage) time)) := by
      simpa only [Nat.nestedExtraction, ← stagesEqual, Function.comp_def, extractions] using
        convergence
    exact UniformLpConvergenceOn.diagonal
      (sequence := fun index time => biotSavart (sequence index time))
      (limit := fun time => biotSavart (localLimit stage (stages stage) time))
      extractionsIncreasing (stage + 1) rewritten

theorem ContinuousInLpOn.mono {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    {horizon smaller : ℝ} {exponent : ℝ≥0∞} {field : ℝ → Plane → Value}
    (continuity : ContinuousInLpOn horizon exponent field) (ordered : smaller ≤ horizon) :
    ContinuousInLpOn smaller exponent field := by
  obtain ⟨bound, membership, continuous⟩ := continuity
  letI : Fact (1 ≤ exponent) := ⟨bound⟩
  let inclusion : Icc (0 : ℝ) smaller → Icc (0 : ℝ) horizon :=
    fun time => ⟨time, time.property.1, time.property.2.trans ordered⟩
  have inclusionContinuous : Continuous inclusion :=
    continuous_subtype_val.subtype_mk (fun time =>
      ⟨time.property.1, time.property.2.trans ordered⟩)
  exact ⟨bound, fun time => membership (inclusion time),
    continuous.comp inclusionContinuous⟩

theorem diagonal_local_limits_compatible
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : GlobalCompactnessHypotheses initial sequence)
    {localLimit : ℕ → Evolution}
    (solutions : ∀ stage : ℕ, IsEulerSolutionOn (stage + 1) initial (localLimit stage))
    (convergence : ∀ stage : ℕ, UniformLpConvergenceOn (stage + 1) 1 sequence
      (localLimit stage))
    (first second : ℕ) {time : ℝ} (nonnegative : 0 ≤ time)
    (firstBound : time ≤ first + 1) (secondBound : time ≤ second + 1) :
    localLimit first time =ᵐ[volume] localLimit second time := by
  have firstConvergence := (convergence first).mono (smaller := time) firstBound
  have secondConvergence := (convergence second).mono (smaller := time) secondBound
  apply UniformLpConvergenceOn.ae_eq le_rfl firstConvergence secondConvergence
    (show time ∈ Icc 0 time from ⟨nonnegative, le_rfl⟩)
  · intro index
    exact (hypotheses.integrable index time nonnegative).aestronglyMeasurable
  · exact ((solutions first).memLp (exponent := 1) le_rfl
      ⟨nonnegative, firstBound⟩).aestronglyMeasurable
  · exact ((solutions second).memLp (exponent := 1) le_rfl
      ⟨nonnegative, secondBound⟩).aestronglyMeasurable

theorem glued_limit_aestronglyMeasurable
    {initial : Vorticity} {localLimit : ℕ → Evolution}
    (solutions : ∀ stage : ℕ, IsEulerSolutionOn (stage + 1) initial (localLimit stage))
    (horizon : ℝ) :
    AEStronglyMeasurable
      (fun point : ℝ × Plane => localLimit (Nat.ceil point.1) point.1 point.2)
      (spacetimeMeasure horizon) := by
  let pieces : ℕ → Set (ℝ × Plane) := fun stage => {point | Nat.ceil point.1 = stage}
  have cover : (⋃ stage, pieces stage) = univ := by
    ext point
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨Nat.ceil point.1, rfl⟩
  have onPiece : ∀ stage, AEStronglyMeasurable
      (fun point : ℝ × Plane => localLimit (Nat.ceil point.1) point.1 point.2)
      ((spacetimeMeasure horizon).restrict (pieces stage)) := by
    intro stage
    have measurablePiece : MeasurableSet (pieces stage) :=
      (Nat.measurable_ceil.comp measurable_fst) (measurableSet_singleton stage)
    have dominated : (spacetimeMeasure horizon).restrict (pieces stage) ≤
        spacetimeMeasure (stage + 1) := by
      simp only [spacetimeMeasure, Measure.restrict_prod_eq_prod_univ]
      rw [Measure.restrict_restrict measurablePiece]
      apply Measure.restrict_mono _ le_rfl
      intro point inside
      refine ⟨⟨inside.2.1.1, ?_⟩, mem_univ _⟩
      have ceiling : Nat.ceil point.1 = stage := inside.1
      have bound := Nat.le_ceil point.1
      rw [ceiling] at bound
      linarith
    apply ((solutions stage).2.2.2.2.2.2.1.aestronglyMeasurable.mono_measure dominated).congr
    filter_upwards [ae_restrict_mem measurablePiece] with point inside
    simp only [pieces, mem_setOf_eq] at inside
    simp only [Function.uncurry, inside]
  simpa only [cover, Measure.restrict_univ] using AEStronglyMeasurable.iUnion onPiece

theorem spacetime_ae_eq_of_slice_ae_eq
    {horizon : ℝ} {first second : Evolution}
    (firstMeasurable : AEStronglyMeasurable (Function.uncurry first) (spacetimeMeasure horizon))
    (secondMeasurable : AEStronglyMeasurable (Function.uncurry second) (spacetimeMeasure horizon))
    (equal : ∀ time ∈ Ioo 0 horizon, first time =ᵐ[volume] second time) :
    Function.uncurry first =ᵐ[spacetimeMeasure horizon] Function.uncurry second := by
  have firstSlices := Measure.ae_ae_of_ae_prod firstMeasurable.ae_eq_mk
  have secondSlices := Measure.ae_ae_of_ae_prod secondMeasurable.ae_eq_mk
  have measurableEqual : MeasurableSet {point |
      firstMeasurable.mk (Function.uncurry first) point =
        secondMeasurable.mk (Function.uncurry second) point} :=
    measurableSet_eq_fun firstMeasurable.stronglyMeasurable_mk.measurable
      secondMeasurable.stronglyMeasurable_mk.measurable
  have representativesEqual : firstMeasurable.mk (Function.uncurry first) =ᵐ[spacetimeMeasure horizon]
      secondMeasurable.mk (Function.uncurry second) := by
    apply (Measure.ae_prod_iff_ae_ae measurableEqual).mpr
    filter_upwards [firstSlices, secondSlices, ae_restrict_mem measurableSet_Ioo]
      with time firstSlice secondSlice inside
    filter_upwards [firstSlice, secondSlice, equal time inside] with position firstEqual
      secondEqual sliceEqual
    exact firstEqual.symm.trans (sliceEqual.trans secondEqual)
  exact firstMeasurable.ae_eq_mk.trans
    (representativesEqual.trans secondMeasurable.ae_eq_mk.symm)

theorem WeakTransportOn.congr_ae {horizon : ℝ} {initial : Vorticity}
    {first second : Evolution} {firstVelocity secondVelocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial first firstVelocity)
    (equal : Function.uncurry first =ᵐ[spacetimeMeasure horizon] Function.uncurry second)
    (velocityEqual : ∀ time ∈ Ioo 0 horizon, firstVelocity time = secondVelocity time) :
    WeakTransportOn horizon initial second secondVelocity := by
  intro test admissible
  have integrandEqual :
      (fun point : ℝ × Plane => first point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (firstVelocity point.1 point.2)))
      =ᵐ[spacetimeMeasure horizon]
      (fun point : ℝ × Plane => second point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (secondVelocity point.1 point.2))) := by
    have inside : ∀ᵐ point ∂spacetimeMeasure horizon, point.1 ∈ Ioo 0 horizon := by
      simpa only [spacetimeMeasure, Measure.restrict_prod_eq_prod_univ] using
        (ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)).mono
          (fun point membership => membership.1)
    filter_upwards [equal, inside] with point equal inside
    simp only [Function.uncurry] at equal
    rw [equal, velocityEqual point.1 inside]
  obtain ⟨integrability, initialIntegrability, identity⟩ := transport test admissible
  exact ⟨integrability.congr integrandEqual, initialIntegrability,
    (integral_congr_ae integrandEqual).symm ▸ identity⟩

theorem WeakMomentumOn.congr {horizon : ℝ} {initial : Velocity}
    {first second : ℝ → Velocity}
    (momentum : WeakMomentumOn horizon initial first)
    (equal : ∀ time ∈ Ioo 0 horizon, first time = second time) :
    WeakMomentumOn horizon initial second := by
  intro test admissible
  have inside : ∀ᵐ point ∂spacetimeMeasure horizon, point.1 ∈ Ioo 0 horizon := by
    simpa only [spacetimeMeasure, Measure.restrict_prod_eq_prod_univ] using
      (ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)).mono
        (fun point membership => membership.1)
  have integrandEqual :
      (fun point : ℝ × Plane => @inner ℝ Plane _ (first point.1 point.2)
        (timeDerivative test point + spatialDerivative test point (first point.1 point.2)))
      =ᵐ[spacetimeMeasure horizon]
      (fun point : ℝ × Plane => @inner ℝ Plane _ (second point.1 point.2)
        (timeDerivative test point + spatialDerivative test point (second point.1 point.2))) := by
    filter_upwards [inside] with point inside
    rw [equal point.1 inside]
  obtain ⟨integrability, initialIntegrability, identity⟩ := momentum test admissible
  exact ⟨integrability.congr integrandEqual, initialIntegrability,
    (integral_congr_ae integrandEqual).symm ▸ identity⟩

theorem IsEulerSolutionOn.congr_ae {horizon : ℝ} {initial : Vorticity}
    {first second : Evolution}
    (solution : IsEulerSolutionOn horizon initial first) (nonnegative : 0 ≤ horizon)
    (secondMeasurable : AEStronglyMeasurable (Function.uncurry second) (spacetimeMeasure horizon))
    (equal : ∀ time ∈ Icc 0 horizon, first time =ᵐ[volume] second time) :
    IsEulerSolutionOn horizon initial second := by
  rcases solution with ⟨initialEqual, continuous, velocityContinuous, integrability,
    conservation, divergence, transport, renormalization, momentum⟩
  have velocityEqual : ∀ time ∈ Icc 0 horizon,
      biotSavart (first time) = biotSavart (second time) :=
    fun time inside => biotSavart_congr_ae (equal time inside)
  have spacetimeEqual := spacetime_ae_eq_of_slice_ae_eq transport.aestronglyMeasurable
    secondMeasurable (fun time inside => equal time ⟨inside.1.le, inside.2.le⟩)
  refine ⟨(equal 0 ⟨le_rfl, nonnegative⟩).symm.trans initialEqual,
    fun exponent bound => (continuous exponent bound).congr_ae equal,
    velocityContinuous.congr_ae (fun time inside =>
      Filter.EventuallyEq.of_eq (velocityEqual time inside)),
    fun time inside => (integrability time inside).congr_ae (equal time inside),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro exponent bound time inside
    exact (eLpNorm_congr_ae (equal time inside)).symm.trans
      (conservation exponent bound time inside)
  · intro time inside test smooth compact
    rw [← velocityEqual time inside]
    exact divergence time inside test smooth compact
  · exact transport.congr_ae spacetimeEqual
      (fun time inside => velocityEqual time ⟨inside.1.le, inside.2.le⟩)
  · intro function admissible
    apply (renormalization function admissible).congr_ae
      (second := fun time => function ∘ second time)
      (secondVelocity := fun time => biotSavart (second time))
      (spacetimeEqual.mono (fun point equal => congrArg function equal))
      (fun time inside => velocityEqual time ⟨inside.1.le, inside.2.le⟩)
  · exact momentum.congr (fun time inside => velocityEqual time ⟨inside.1.le, inside.2.le⟩)

theorem IsEulerSolutionOn.mono {horizon smaller : ℝ} {initial : Vorticity} {omega : Evolution}
    (solution : IsEulerSolutionOn horizon initial omega) (ordered : smaller ≤ horizon) :
    IsEulerSolutionOn smaller initial omega := by
  rcases solution with ⟨initialEqual, continuous, velocityContinuous, integrability,
    conservation, divergence, transport, renormalization, momentum⟩
  refine ⟨initialEqual, fun exponent bound => (continuous exponent bound).mono ordered,
    velocityContinuous.mono ordered, ?_, ?_, ?_, transport.mono ordered,
    fun function admissible => (renormalization function admissible).mono ordered,
    momentum.mono ordered⟩
  · intro time inside
    exact integrability time ⟨inside.1, inside.2.trans ordered⟩
  · intro exponent bound time inside
    exact conservation exponent bound time ⟨inside.1, inside.2.trans ordered⟩
  · intro time inside
    exact divergence time ⟨inside.1, inside.2.trans ordered⟩

theorem isEulerSolution_of_isEulerSolutionOn {initial : Vorticity} {omega : Evolution}
    (solutions : ∀ horizon : ℝ, 0 < horizon → IsEulerSolutionOn horizon initial omega) :
    IsEulerSolution initial omega := by
  refine ⟨(solutions 1 zero_lt_one).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro exponent bound
    exact continuousInLp_of_continuousInLpOn
      (fun horizon positive => (solutions horizon positive).2.1 exponent bound)
  · exact continuousInLp_of_continuousInLpOn
      (fun horizon positive => (solutions horizon positive).2.2.1)
  · intro time nonnegative
    exact (solutions (time + 1) (by linarith)).2.2.2.1 time
      ⟨nonnegative, by linarith⟩
  · intro exponent bound time nonnegative
    exact (solutions (time + 1) (by linarith)).2.2.2.2.1 exponent bound time
      ⟨nonnegative, by linarith⟩
  · intro time nonnegative
    exact (solutions (time + 1) (by linarith)).2.2.2.2.2.1 time
      ⟨nonnegative, by linarith⟩
  · intro horizon positive
    exact (solutions horizon positive).2.2.2.2.2.2.1
  · intro function admissible horizon positive
    exact (solutions horizon positive).2.2.2.2.2.2.2.1 function admissible
  · intro horizon positive
    exact (solutions horizon positive).2.2.2.2.2.2.2.2

theorem exists_global_limit_local_ae (compactness : Lemma81Statement)
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : GlobalCompactnessHypotheses initial sequence) :
    ∃ subsequence : ℕ → ℕ, ∃ localLimit : ℕ → Evolution, ∃ limit : Evolution,
      StrictMono subsequence ∧
      (∀ stage : ℕ, IsEulerSolutionOn (stage + 1) initial (localLimit stage)) ∧
      (∀ stage : ℕ, ∀ time ∈ Icc (0 : ℝ) (stage + 1),
        localLimit stage time =ᵐ[volume] limit time) ∧
      (∀ stage : ℕ, ∀ exponent : ℝ, 1 ≤ exponent →
        UniformLpConvergenceOn (stage + 1) (ENNReal.ofReal exponent)
          (sequence ∘ subsequence) limit) ∧
      (∀ stage : ℕ, UniformLpConvergenceOn (stage + 1) 2
        (fun index time => biotSavart (sequence (subsequence index) time))
        (fun time => biotSavart (limit time))) ∧
      (∀ horizon : ℝ, AEStronglyMeasurable (Function.uncurry limit)
        (spacetimeMeasure horizon)) := by
  obtain ⟨subsequence, localLimit, increasing, properties⟩ :=
    exists_diagonal_local_limits compactness hypotheses
  let limit : Evolution := fun time => localLimit (Nat.ceil time) time
  have equality : ∀ stage : ℕ, ∀ time ∈ Icc (0 : ℝ) (stage + 1),
      localLimit stage time =ᵐ[volume] limit time := by
    intro stage time inside
    apply diagonal_local_limits_compatible (hypotheses.subsequence increasing)
      (fun stage => (properties stage).1)
      (fun stage => by simpa using (properties stage).2.1 1 le_rfl)
      stage (Nat.ceil time) inside.1 inside.2
    exact (Nat.le_ceil time).trans (by linarith)
  refine ⟨subsequence, localLimit, limit, increasing,
    fun stage => (properties stage).1, equality, ?_, ?_, ?_⟩
  · intro stage exponent exponentBound
    exact ((properties stage).2.1 exponent exponentBound).congr_limit (equality stage)
  · intro stage
    apply ((properties stage).2.2).congr_limit
    intro time inside
    exact Filter.EventuallyEq.of_eq (biotSavart_congr_ae (equality stage time inside))
  · exact glued_limit_aestronglyMeasurable (fun stage => (properties stage).1)

theorem globalization : GlobalizationObligation := by
  intro compactness initial sequence hypotheses
  obtain ⟨subsequence, localLimit, limit, increasing, localSolutions, equality,
    vorticityConvergence, velocityConvergence, measurable⟩ :=
    exists_global_limit_local_ae compactness hypotheses
  have horizonBound : ∀ horizon : ℝ, horizon ≤ (Nat.ceil horizon : ℝ) + 1 := by
    intro horizon
    exact (Nat.le_ceil horizon).trans (by linarith)
  have globalSolution : IsEulerSolution initial limit := by
    apply isEulerSolution_of_isEulerSolutionOn
    intro horizon positive
    apply ((localSolutions (Nat.ceil horizon)).mono (horizonBound horizon)).congr_ae
      positive.le (measurable horizon)
    intro time inside
    exact equality (Nat.ceil horizon) time
      ⟨inside.1, inside.2.trans (horizonBound horizon)⟩
  refine ⟨subsequence, limit, increasing, globalSolution, ?_, ?_, ?_⟩
  · intro horizon positive exponent bound
    exact (vorticityConvergence (Nat.ceil horizon) exponent bound).mono (horizonBound horizon)
  · intro horizon positive
    exact (velocityConvergence (Nat.ceil horizon)).mono (horizonBound horizon)
  · intro time nonnegative
    apply UniformLpConvergenceOn.tendsto_l1Distance
      (by simpa using vorticityConvergence (Nat.ceil time) 1 le_rfl)
      ⟨nonnegative, horizonBound time⟩
    · intro index
      exact (hypotheses.integrable (subsequence index) time nonnegative).aestronglyMeasurable
    · exact (globalSolution.integrable time nonnegative).aestronglyMeasurable

end EulerNonuniqueness
