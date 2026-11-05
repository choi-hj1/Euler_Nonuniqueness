import EulerNonuniqueness.General.L2PairingContinuity
import EulerNonuniqueness.General.WeakSequentialCompactness
import EulerNonuniqueness.Section8.Compactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.exists_weakL2_vorticity_subsequence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ limit : Vorticity, MemLp limit 2 volume ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ test : Vorticity,
        MemLp test 2 volume → Tendsto
          (fun index => ∫ position, sequence (parameters (subsequence index)).1
            (parameters (subsequence index)).2 position * test position)
          atTop (𝓝 (∫ position, limit position * test position)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let members : ∀ index : ℕ, MemLp (sequence (parameters index).1 (parameters index).2) 2 volume :=
    fun index => (hypotheses.2.2 (parameters index).1).2.1.1
      (parameters index).2 (parameters index).2.property
  let fields : ℕ → Lp ℝ 2 (volume : Measure Plane) := fun index =>
    (members index).toLp (sequence (parameters index).1 (parameters index).2)
  obtain ⟨bound, boundFinite, bounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 2)
  have normBound (index : ℕ) : ‖fields index‖ ≤ bound.toReal := by
    change ‖(members index).toLp (sequence (parameters index).1 (parameters index).2)‖ ≤ _
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono boundFinite.ne (by
      simpa using bounded (parameters index).1 (parameters index).2 (parameters index).2.property)
  obtain ⟨limit, limitBound, subsequence, increasing, converges⟩ :=
    exists_weakly_convergent_subsequence_of_bounded normBound
  refine ⟨limit, Lp.memLp limit, subsequence, increasing, ?_⟩
  intro test testMember
  have pairingEquality (index : ℕ) : ⟪fields index, testMember.toLp test⟫_ℝ =
      ∫ position, sequence (parameters index).1 (parameters index).2 position * test position :=
    inner_toLp_eq_integral_mul (members index) testMember
  have limitEquality : ⟪limit, testMember.toLp test⟫_ℝ =
      ∫ position, limit position * test position := by
    have equality : (Lp.memLp limit).toLp (limit : Plane → ℝ) = limit := by simp
    calc
      _ = ⟪(Lp.memLp limit).toLp (limit : Plane → ℝ), testMember.toLp test⟫_ℝ :=
        congrArg (fun field => ⟪field, testMember.toLp test⟫_ℝ) equality.symm
      _ = _ := inner_toLp_eq_integral_mul (Lp.memLp limit) testMember
  simpa only [pairingEquality, limitEquality] using converges (testMember.toLp test)

end EulerNonuniqueness
