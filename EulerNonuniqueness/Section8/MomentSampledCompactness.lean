import EulerNonuniqueness.Section8.MomentCompactnessData
import EulerNonuniqueness.General.WeakSequentialCompactness
import EulerNonuniqueness.General.L2PairingContinuity
import EulerNonuniqueness.General.WeakSupport
import EulerNonuniqueness.General.LpWeakBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace EulerNonuniqueness

theorem MomentCompactnessData.exists_weakL2_vorticity_subsequence
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ limit : Vorticity, MemLp limit 2 volume ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ test : Vorticity,
        MemLp test 2 volume → Tendsto
          (fun index => ∫ position, sequence (parameters (subsequence index)).1
            (parameters (subsequence index)).2 position * test position)
          atTop (𝓝 (∫ position, limit position * test position)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let members : ∀ index : ℕ, MemLp (sequence (parameters index).1 (parameters index).2) 2 volume :=
    fun index => by
      simpa using (data.members 2 (by norm_num) (parameters index).1
        (parameters index).2 (parameters index).2.property)
  let fields : ℕ → Lp ℝ 2 (volume : Measure Plane) := fun index =>
    (members index).toLp (sequence (parameters index).1 (parameters index).2)
  obtain ⟨bound, boundFinite, bounded⟩ := data.normBounded 2 (by norm_num)
  have normBound (index : ℕ) : ‖fields index‖ ≤ bound.toReal := by
    change ‖(members index).toLp (sequence (parameters index).1 (parameters index).2)‖ ≤ _
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono boundFinite.ne (by
      simpa using bounded (parameters index).1 (parameters index).2 (parameters index).2.property)
  obtain ⟨limit, _, subsequence, increasing, converges⟩ :=
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

theorem MomentCompactnessData.exists_supported_weakL2_vorticity_subsequence
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ limit : Vorticity,
      MemLp limit 2 volume ∧ Integrable limit ∧ HasCompactSupport limit ∧
      Function.support limit ⊆ Metric.closedBall 0 radius ∧ (∫ position, limit position) = 0 ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ test : Vorticity,
        MemLp test 2 volume → Tendsto
          (fun index => ∫ position, sequence (parameters (subsequence index)).1
            (parameters (subsequence index)).2 position * test position)
          atTop (𝓝 (∫ position, limit position * test position)) := by
  obtain ⟨radius, radiusPositive, supported⟩ := data.supported
  obtain ⟨rawLimit, rawMember, subsequence, increasing, weak⟩ :=
    data.exists_weakL2_vorticity_subsequence parameters
  let region := Metric.closedBall (0 : Plane) radius
  let limit := region.indicator rawLimit
  have regionMeasurable : MeasurableSet region := measurableSet_closedBall
  have regionFinite : volume region ≠ ∞ := (isCompact_closedBall (0 : Plane) radius).measure_lt_top.ne
  have limitSupported : Function.support limit ⊆ region := support_indicator_subset
  have limitIntegrable : Integrable limit :=
    integrable_indicator_of_memLp_two rawMember regionMeasurable regionFinite
  have weakLimit (test : Vorticity) (testMember : MemLp test 2 volume) : Tendsto
      (fun index => ∫ position, sequence (parameters (subsequence index)).1
        (parameters (subsequence index)).2 position * test position)
      atTop (𝓝 (∫ position, limit position * test position)) :=
    tendsto_integral_mul_indicator_limit_of_support regionMeasurable
      (fun index => supported (parameters (subsequence index)).1
        (parameters (subsequence index)).2 (parameters (subsequence index)).2.property)
      weak testMember
  have meanZero : (∫ position, limit position) = 0 := by
    let test : Vorticity := region.indicator (fun _ => 1)
    have testMember : MemLp test 2 volume := memLp_indicator_const 2 regionMeasurable 1 (Or.inr regionFinite)
    have sourceEquality (index : ℕ) : (fun position =>
        sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2 position * test position) =
        sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2 := by
      funext position
      by_cases inside : position ∈ region
      · simp [test, inside]
      · have sourceZero := Function.nmem_support.mp (fun inSupport => inside
          (supported (parameters (subsequence index)).1 (parameters (subsequence index)).2
            (parameters (subsequence index)).2.property inSupport))
        simp [test, inside, sourceZero]
    have limitEquality : (fun position => limit position * test position) = limit := by
      funext position
      by_cases inside : position ∈ region <;> simp [limit, test, inside]
    have zero (index : ℕ) : (∫ position, sequence (parameters (subsequence index)).1
        (parameters (subsequence index)).2 position) = 0 :=
      data.zeroMean (parameters (subsequence index)).1 (parameters (subsequence index)).2
        (parameters (subsequence index)).2.property
    have converges := weakLimit test testMember
    simp only [sourceEquality, limitEquality, zero] at converges
    exact tendsto_nhds_unique converges tendsto_const_nhds
  refine ⟨radius, radiusPositive, limit, rawMember.indicator regionMeasurable,
    limitIntegrable, ?_, limitSupported, meanZero, subsequence, increasing, weakLimit⟩
  exact (isCompact_closedBall (0 : Plane) radius).of_isClosed_subset (isClosed_tsupport limit)
    (closure_minimal limitSupported Metric.isClosed_closedBall)

theorem MomentCompactnessData.exists_allLp_weakL2_vorticity_subsequence
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ limit : Vorticity,
      HasCompactSupport limit ∧ Function.support limit ⊆ Metric.closedBall 0 radius ∧
      (∫ position, limit position) = 0 ∧
      (∀ exponent : ℝ, 1 ≤ exponent → MemLp limit (ENNReal.ofReal exponent) volume) ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ test : Vorticity,
        MemLp test 2 volume → Tendsto
          (fun index => ∫ position, sequence (parameters (subsequence index)).1
            (parameters (subsequence index)).2 position * test position)
          atTop (𝓝 (∫ position, limit position * test position)) := by
  obtain ⟨radius, positive, limit, limitMember, _, compact,
    supported, meanZero, subsequence, increasing, weak⟩ := data.exists_supported_weakL2_vorticity_subsequence parameters
  refine ⟨radius, positive, limit, compact, supported, meanZero, ?_, subsequence, increasing, weak⟩
  intro exponent exponentBound
  obtain ⟨bound, finite, bounded⟩ := data.normBounded exponent exponentBound
  have normBound : eLpNorm limit (ENNReal.ofReal exponent) volume ≤ bound :=
    eLpNorm_le_of_weakL2_tendsto_functions
      (fun index => by
        simpa using (data.members 2 (by norm_num) (parameters (subsequence index)).1
          (parameters (subsequence index)).2 (parameters (subsequence index)).2.property))
      limitMember (by exact_mod_cast ENNReal.ofReal_le_ofReal exponentBound)
      (fun index => bounded (parameters (subsequence index)).1
        (parameters (subsequence index)).2 (parameters (subsequence index)).2.property) weak
  exact ⟨limitMember.aestronglyMeasurable, normBound.trans_lt finite⟩

end EulerNonuniqueness
