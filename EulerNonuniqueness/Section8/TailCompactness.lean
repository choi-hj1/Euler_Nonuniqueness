import EulerNonuniqueness.Section8.Globalization

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace EulerNonuniqueness

def TailCompactnessHypotheses (initial : Vorticity) (sequence : ℕ → Evolution) : Prop :=
  ∀ horizon : ℝ, 0 < horizon → ∃ cutoff : ℕ,
    LocalCompactnessHypotheses horizon initial (fun index => sequence (index + cutoff))

theorem TailCompactnessHypotheses.subsequence {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : TailCompactnessHypotheses initial sequence)
    {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence) :
    TailCompactnessHypotheses initial (sequence ∘ subsequence) := by
  intro horizon positive
  obtain ⟨cutoff, localHypotheses⟩ := hypotheses horizon positive
  let tail : ℕ → ℕ := fun index => subsequence (index + cutoff) - cutoff
  have above (index : ℕ) : cutoff ≤ subsequence (index + cutoff) :=
    (Nat.le_add_left cutoff index).trans (increasing.id_le (index + cutoff))
  have tailIncreasing : StrictMono tail := by
    intro first second ordered
    have orderedImage := increasing (Nat.add_lt_add_right ordered cutoff)
    have firstAbove := above first
    have secondAbove := above second
    dsimp only [tail]
    omega
  refine ⟨cutoff, ?_⟩
  have extracted := localHypotheses.subsequence tailIncreasing
  have equality : (fun index => sequence (index + cutoff)) ∘ tail =
      (fun index => (sequence ∘ subsequence) (index + cutoff)) := by
    funext index
    simp only [Function.comp_apply, tail, Nat.sub_add_cancel (above index)]
  rw [equality] at extracted
  exact extracted

set_option maxHeartbeats 800000 in
theorem exists_diagonal_tail_local_limits (compactness : Lemma81Statement)
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : TailCompactnessHypotheses initial sequence) :
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
    obtain ⟨cutoff, localHypotheses⟩ := (hypotheses.subsequence previous.property) (stage + 1) (by positivity)
    obtain ⟨subsequence, limit, increasing, solution, vorticityConverges, velocityConverges⟩ :=
      compactness (stage + 1) (by positivity) initial
        (fun index => (sequence ∘ previous.val) (index + cutoff)) localHypotheses
    refine ⟨fun index => subsequence index + cutoff, limit,
      fun first second ordered => Nat.add_lt_add_right (increasing ordered) cutoff, solution, ?_, ?_⟩
    · exact vorticityConverges
    · exact velocityConverges
  choose next localLimit nextIncreasing localSolution vorticityConvergence velocityConvergence using extract
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
      simpa only [Nat.nestedExtraction, ← stagesEqual, Function.comp_assoc, extractions] using convergence
    exact UniformLpConvergenceOn.diagonal (sequence := sequence)
      (limit := localLimit stage (stages stage)) extractionsIncreasing (stage + 1) rewritten
  · have convergence := velocityConvergence stage (stages stage)
    have rewritten : UniformLpConvergenceOn (stage + 1) 2
        ((fun index time => biotSavart (sequence index time)) ∘ Nat.nestedExtraction extractions (stage + 1))
        (fun time => biotSavart (localLimit stage (stages stage) time)) := by
      simpa only [Nat.nestedExtraction, ← stagesEqual, Function.comp_def, extractions] using convergence
    exact UniformLpConvergenceOn.diagonal
      (sequence := fun index time => biotSavart (sequence index time))
      (limit := fun time => biotSavart (localLimit stage (stages stage) time))
      extractionsIncreasing (stage + 1) rewritten

theorem diagonal_tail_local_limits_compatible
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : TailCompactnessHypotheses initial sequence)
    {localLimit : ℕ → Evolution}
    (solutions : ∀ stage : ℕ, IsEulerSolutionOn (stage + 1) initial (localLimit stage))
    (convergence : ∀ stage : ℕ, UniformLpConvergenceOn (stage + 1) 1 sequence (localLimit stage))
    (first second : ℕ) {time : ℝ} (nonnegative : 0 ≤ time)
    (firstBound : time ≤ first + 1) (secondBound : time ≤ second + 1) :
    localLimit first time =ᵐ[volume] localLimit second time := by
  obtain ⟨cutoff, localHypotheses⟩ := hypotheses (time + 1) (by positivity)
  have shiftIncreasing : StrictMono (fun index : ℕ => index + cutoff) :=
    fun _ _ ordered => Nat.add_lt_add_right ordered cutoff
  apply UniformLpConvergenceOn.ae_eq le_rfl
    (((convergence first).subsequence shiftIncreasing).mono firstBound)
    (((convergence second).subsequence shiftIncreasing).mono secondBound)
    (show time ∈ Icc 0 time from ⟨nonnegative, le_rfl⟩)
  · intro index
    exact (localHypotheses.2.2 index).2.1.1 time ⟨nonnegative, by linarith⟩ |>.aestronglyMeasurable
  · exact ((solutions first).memLp (exponent := 1) le_rfl ⟨nonnegative, firstBound⟩).aestronglyMeasurable
  · exact ((solutions second).memLp (exponent := 1) le_rfl ⟨nonnegative, secondBound⟩).aestronglyMeasurable

end EulerNonuniqueness
