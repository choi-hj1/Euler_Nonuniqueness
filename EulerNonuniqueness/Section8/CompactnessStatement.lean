import EulerNonuniqueness.Definitions

/-!
# The compactness step, Lemma 8.1

`Lemma81Statement` is the local compactness theorem stated in the manuscript.
Its specification is proved by `lemma81` in `Section8.CompactnessProof`. The global
diagonal-extraction implication is proved in `Section8.Globalization`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped ContDiff

namespace EulerNonuniqueness

def ContinuousInLpOn {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    (horizon : ℝ) (exponent : ℝ≥0∞) (field : ℝ → Plane → Value) : Prop :=
  ∃ exponentBound : 1 ≤ exponent,
    letI : Fact (1 ≤ exponent) := ⟨exponentBound⟩
    ∃ membership : ∀ time : Icc 0 horizon, MemLp (field time) exponent volume,
      Continuous (fun time : Icc 0 horizon => (membership time).toLp (field time))

def WeakL2ContinuousOn (horizon : ℝ) (omega : Evolution) : Prop :=
  (∀ time ∈ Icc 0 horizon, MemLp (omega time) 2 volume) ∧
    ∀ test : Vorticity, MemLp test 2 volume →
      Continuous (fun time : Icc 0 horizon => ∫ position, omega time position * test position)

def InitialLpConvergence (sequence : ℕ → Evolution) (initial : Vorticity) : Prop :=
  (∀ exponent : ℝ, 1 ≤ exponent → MemLp initial (ENNReal.ofReal exponent) volume) ∧
    ∀ exponent : ℝ, 1 ≤ exponent →
      Tendsto (fun index => eLpNorm (sequence index 0 - initial)
        (ENNReal.ofReal exponent) volume) atTop (𝓝 0)

/-- Uniform strong convergence on the stated time interval, expressed by its norm. -/
def UniformLpConvergenceOn {Value : Type*} [NormedAddCommGroup Value]
    (horizon : ℝ) (exponent : ℝ≥0∞)
    (sequence : ℕ → ℝ → Plane → Value) (limit : ℝ → Plane → Value) : Prop :=
  ∀ tolerance : ℝ, 0 < tolerance → ∃ cutoff : ℕ, ∀ index, cutoff ≤ index →
    ∀ time ∈ Icc 0 horizon,
      eLpNorm (sequence index time - limit time) exponent volume < ENNReal.ofReal tolerance

def LocalCompactnessHypotheses (horizon : ℝ) (initial : Vorticity)
    (sequence : ℕ → Evolution) : Prop :=
  InitialLpConvergence sequence initial ∧
    (∃ radius : ℝ, 0 < radius ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
      Function.support (sequence index time) ⊆ Metric.closedBall 0 radius) ∧
    ∀ index,
      WeakTransportOn horizon (sequence index 0) (sequence index)
        (fun time => biotSavart (sequence index time)) ∧
      WeakL2ContinuousOn horizon (sequence index) ∧
      (∀ time ∈ Icc 0 horizon, BiotSavartIntegrable (sequence index time) ∧
        (∫ position, sequence index time position) = 0) ∧
      ∀ exponent : ℝ, 1 ≤ exponent → ∀ time ∈ Icc 0 horizon,
        MemLp (sequence index time) (ENNReal.ofReal exponent) volume ∧
        eLpNorm (sequence index time) (ENNReal.ofReal exponent) volume =
          eLpNorm (sequence index 0) (ENNReal.ofReal exponent) volume

def IsEulerSolutionOn (horizon : ℝ) (initial : Vorticity) (omega : Evolution) : Prop :=
  (omega 0 =ᵐ[volume] initial) ∧
    (∀ exponent : ℝ, 1 ≤ exponent →
      ContinuousInLpOn horizon (ENNReal.ofReal exponent) omega) ∧
    ContinuousInLpOn horizon 2 (fun time => biotSavart (omega time)) ∧
    (∀ time ∈ Icc 0 horizon, BiotSavartIntegrable (omega time)) ∧
    (∀ exponent : ℝ, 1 ≤ exponent → ∀ time ∈ Icc 0 horizon,
      eLpNorm (omega time) (ENNReal.ofReal exponent) volume =
        eLpNorm initial (ENNReal.ofReal exponent) volume) ∧
    (∀ time ∈ Icc 0 horizon, ∀ test : Plane → ℝ,
      ContDiff ℝ ∞ test → HasCompactSupport test →
      Integrable (fun position => fderiv ℝ test position (biotSavart (omega time) position)) ∧
      (∫ position, fderiv ℝ test position (biotSavart (omega time) position)) = 0) ∧
    WeakTransportOn horizon initial omega (fun time => biotSavart (omega time)) ∧
    (∀ renormalization, AdmissibleRenormalization renormalization →
      WeakTransportOn horizon (renormalization ∘ initial)
        (fun time => renormalization ∘ omega time)
        (fun time => biotSavart (omega time))) ∧
    WeakMomentumOn horizon (biotSavart initial) (fun time => biotSavart (omega time))

/-- Frozen manuscript Lemma 8.1, proved by `lemma81`. -/
def Lemma81Statement : Prop :=
  ∀ horizon : ℝ, 0 < horizon → ∀ initial sequence,
    LocalCompactnessHypotheses horizon initial sequence →
    ∃ subsequence : ℕ → ℕ, ∃ limit : Evolution,
      StrictMono subsequence ∧ IsEulerSolutionOn horizon initial limit ∧
      (∀ exponent : ℝ, 1 ≤ exponent → UniformLpConvergenceOn horizon
        (ENNReal.ofReal exponent) (sequence ∘ subsequence) limit) ∧
      UniformLpConvergenceOn horizon 2
        (fun index time => biotSavart (sequence (subsequence index) time))
        (fun time => biotSavart (limit time))

/-- These hypotheses concern the actual globally extended finite-patch sequence. -/
def GlobalCompactnessHypotheses (initial : Vorticity) (sequence : ℕ → Evolution) : Prop :=
  ∀ horizon : ℝ, 0 < horizon → LocalCompactnessHypotheses horizon initial sequence

def GlobalCompactnessConclusion (initial : Vorticity) (sequence : ℕ → Evolution) : Prop :=
  ∃ subsequence : ℕ → ℕ, ∃ limit : Evolution,
    StrictMono subsequence ∧ IsEulerSolution initial limit ∧
    (∀ horizon : ℝ, 0 < horizon → ∀ exponent : ℝ, 1 ≤ exponent →
      UniformLpConvergenceOn horizon (ENNReal.ofReal exponent) (sequence ∘ subsequence) limit) ∧
    (∀ horizon : ℝ, 0 < horizon → UniformLpConvergenceOn horizon 2
      (fun index time => biotSavart (sequence (subsequence index) time))
      (fun time => biotSavart (limit time))) ∧
    ∀ time : ℝ, 0 ≤ time →
      Tendsto (fun index => l1Distance (sequence (subsequence index) time) (limit time))
        atTop (𝓝 0)

/-- The global diagonal passage after Lemma 8.1, proved by `globalization`.
The final clause of the conclusion is the `p=1` consequence used for observation. -/
def GlobalizationObligation : Prop :=
  Lemma81Statement → ∀ initial sequence,
    GlobalCompactnessHypotheses initial sequence → GlobalCompactnessConclusion initial sequence

theorem IsEulerSolution.integrable {initial : Vorticity} {omega : Evolution}
    (solution : IsEulerSolution initial omega) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    Integrable (omega time) := by
  obtain ⟨exponentBound, membership, continuous⟩ := solution.2.1 1 le_rfl
  have member := membership (⟨time, timeNonnegative⟩ : ℝ≥0)
  exact memLp_one_iff_integrable.mp (by simpa using member)

theorem GlobalCompactnessHypotheses.integrable {initial : Vorticity}
    {sequence : ℕ → Evolution} (hypotheses : GlobalCompactnessHypotheses initial sequence)
    (index : ℕ) (time : ℝ) (timeNonnegative : 0 ≤ time) : Integrable (sequence index time) := by
  have localHypotheses := hypotheses (time + 1) (by linarith)
  have member := (localHypotheses.2.2 index).2.2.2 1 le_rfl time
    ⟨timeNonnegative, by linarith⟩
  exact memLp_one_iff_integrable.mp (by simpa using member.1)

end EulerNonuniqueness
