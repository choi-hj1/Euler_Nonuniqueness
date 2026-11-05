import EulerNonuniqueness.General.WeakSupport
import EulerNonuniqueness.Section8.WeakVorticityCompactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.exists_supported_weakL2_vorticity_subsequence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ limit : Vorticity,
      MemLp limit 2 volume ∧ Integrable limit ∧ HasCompactSupport limit ∧
      Function.support limit ⊆ Metric.closedBall 0 radius ∧ (∫ position, limit position) = 0 ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ test : Vorticity,
        MemLp test 2 volume → Tendsto
          (fun index => ∫ position, sequence (parameters (subsequence index)).1
            (parameters (subsequence index)).2 position * test position)
          atTop (𝓝 (∫ position, limit position * test position)) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  obtain ⟨rawLimit, rawMember, subsequence, increasing, weak⟩ :=
    hypotheses.exists_weakL2_vorticity_subsequence horizonNonnegative parameters
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
        sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2 position *
          test position) =
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
      ((hypotheses.2.2 (parameters (subsequence index)).1).2.2.1
        (parameters (subsequence index)).2 (parameters (subsequence index)).2.property).2
    have converges := weakLimit test testMember
    simp only [sourceEquality, limitEquality, zero] at converges
    exact tendsto_nhds_unique converges tendsto_const_nhds
  refine ⟨radius, radiusPositive, limit, rawMember.indicator regionMeasurable,
    limitIntegrable, ?_, limitSupported, meanZero, subsequence, increasing, weakLimit⟩
  exact (isCompact_closedBall (0 : Plane) radius).of_isClosed_subset (isClosed_tsupport limit)
    (closure_minimal limitSupported Metric.isClosed_closedBall)

end EulerNonuniqueness
