import EulerNonuniqueness.Section8.TailGlobalization
import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace EulerNonuniqueness

theorem ContinuousInLpOn.weakL2ContinuousOn {horizon : ℝ} {omega : Evolution}
    (continuity : ContinuousInLpOn horizon 2 omega) : WeakL2ContinuousOn horizon omega := by
  obtain ⟨bound, membership, continuous⟩ := continuity
  refine ⟨fun time inside => membership ⟨time, inside⟩, ?_⟩
  intro test testMember
  have pairing : Continuous (fun time : Icc (0 : ℝ) horizon =>
      ⟪(membership time).toLp (omega time), testMember.toLp test⟫_ℝ) :=
    continuous.inner continuous_const
  simpa only [inner_toLp_eq_integral_mul] using pairing

theorem IsEulerSolutionOn.weakL2ContinuousOn {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (solution : IsEulerSolutionOn horizon initial omega) : WeakL2ContinuousOn horizon omega := by
  apply ContinuousInLpOn.weakL2ContinuousOn
  simpa using solution.2.1 2 (by norm_num)

theorem initialLpConvergence_of_common_ae_initial
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (members : ∀ exponent : ℝ, 1 ≤ exponent → MemLp initial (ENNReal.ofReal exponent) volume)
    (equal : ∀ index, sequence index 0 =ᵐ[volume] initial) : InitialLpConvergence sequence initial := by
  refine ⟨members, ?_⟩
  intro exponent _
  have normZero (index : ℕ) : eLpNorm (sequence index 0 - initial) (ENNReal.ofReal exponent) volume = 0 := by
    have difference : sequence index 0 - initial =ᵐ[volume] (0 : Vorticity) := by
      filter_upwards [equal index] with position equality
      simp only [Pi.sub_apply, equality, sub_self, Pi.zero_apply]
    rw [eLpNorm_congr_ae difference, eLpNorm_zero]
  simpa only [normZero] using (tendsto_const_nhds (x := (0 : ℝ≥0∞)))

theorem WeakTransportOn.congr_initial_ae {horizon : ℝ} {initial otherInitial : Vorticity}
    {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity)
    (equal : initial =ᵐ[volume] otherInitial) : WeakTransportOn horizon otherInitial omega velocity := by
  intro test admissible
  obtain ⟨integrable, initialIntegrable, identity⟩ := transport test admissible
  have integrandEqual : (fun position => initial position * test (0, position)) =ᵐ[volume]
      (fun position => otherInitial position * test (0, position)) :=
    equal.mono (fun _ equality => congrArg (fun value => value * _) equality)
  exact ⟨integrable, initialIntegrable.congr integrandEqual,
    (integral_congr_ae integrandEqual) ▸ identity⟩

theorem tailCompactness_of_expanding_euler_solutions
    {initial : Vorticity} {sequence : ℕ → Evolution} (datum : InitialDatum initial)
    (solutions : ∀ index : ℕ, IsEulerSolutionOn (index + 1) initial (sequence index))
    (zeroMean : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1), ∫ position, sequence index time position = 0)
    {radius speed : ℝ} (radiusPositive : 0 < radius) (speedNonnegative : 0 ≤ speed)
    (supported : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1),
      Function.support (sequence index time) ⊆ Metric.closedBall 0 (radius + speed * time)) :
    TailCompactnessHypotheses initial sequence := by
  intro horizon positive
  let cutoff := Nat.ceil horizon
  have ordered (index : ℕ) : horizon ≤ ((index + cutoff : ℕ) : ℝ) + 1 := by
    have ceiling : horizon ≤ (cutoff : ℝ) := Nat.le_ceil horizon
    simp only [Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) index]
  have restricted (index : ℕ) : IsEulerSolutionOn horizon initial (sequence (index + cutoff)) :=
    (solutions (index + cutoff)).mono (ordered index)
  refine ⟨cutoff, initialLpConvergence_of_common_ae_initial datum.2.1
    (fun index => (restricted index).1), ⟨radius + speed * horizon, by positivity, ?_⟩, ?_⟩
  · intro index time inside position nonzero
    have originalInside : time ∈ Icc (0 : ℝ) (((index + cutoff : ℕ) : ℝ) + 1) :=
      ⟨inside.1, inside.2.trans (ordered index)⟩
    exact Metric.closedBall_subset_closedBall
      (add_le_add_left (mul_le_mul_of_nonneg_left inside.2 speedNonnegative) radius)
      (supported (index + cutoff) time originalInside nonzero)
  · intro index
    refine ⟨(restricted index).2.2.2.2.2.2.1.congr_initial_ae (restricted index).1.symm,
      (restricted index).weakL2ContinuousOn, ?_, ?_⟩
    · intro time inside
      exact ⟨(restricted index).2.2.2.1 time inside,
        zeroMean (index + cutoff) time ⟨inside.1, inside.2.trans (ordered index)⟩⟩
    · intro exponent exponentBound time inside
      refine ⟨(restricted index).memLp exponentBound inside, ?_⟩
      exact ((restricted index).2.2.2.2.1 exponent exponentBound time inside).trans
        (eLpNorm_congr_ae (restricted index).1).symm

theorem exists_global_euler_of_expanding_solutions
    {initial : Vorticity} {sequence : ℕ → Evolution} (datum : InitialDatum initial)
    (solutions : ∀ index : ℕ, IsEulerSolutionOn (index + 1) initial (sequence index))
    (zeroMean : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1), ∫ position, sequence index time position = 0)
    {radius speed : ℝ} (radiusPositive : 0 < radius) (speedNonnegative : 0 ≤ speed)
    (supported : ∀ index : ℕ, ∀ time ∈ Icc (0 : ℝ) (index + 1),
      Function.support (sequence index time) ⊆ Metric.closedBall 0 (radius + speed * time)) :
    ∃ omega : Evolution, IsEulerSolution initial omega := by
  obtain ⟨_, omega, _, solution, _⟩ := tail_globalization
    (tailCompactness_of_expanding_euler_solutions datum solutions zeroMean radiusPositive speedNonnegative supported)
  exact ⟨omega, solution⟩

end EulerNonuniqueness
