import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem tendsto_integral_mul_indicator_limit_of_support
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} {sequence : Index → Domain → ℝ} {limit test : Domain → ℝ}
    {region : Set Domain} (measurable : MeasurableSet region)
    (supported : ∀ index, Function.support (sequence index) ⊆ region)
    (weak : ∀ fixedTest : Domain → ℝ, MemLp fixedTest 2 measure →
      Tendsto (fun index => ∫ point, sequence index point * fixedTest point ∂measure)
        filter (𝓝 (∫ point, limit point * fixedTest point ∂measure)))
    (testMember : MemLp test 2 measure) :
    Tendsto (fun index => ∫ point, sequence index point * test point ∂measure)
      filter (𝓝 (∫ point, region.indicator limit point * test point ∂measure)) := by
  have sequenceEquality (index : Index) :
      (fun point => sequence index point * region.indicator test point) =
        (fun point => sequence index point * test point) := by
    funext point
    by_cases inside : point ∈ region
    · rw [indicator_of_mem inside]
    · have sourceZero : sequence index point = 0 :=
        Function.nmem_support.mp (fun inSupport => inside (supported index inSupport))
      simp only [sourceZero, zero_mul]
  have limitEquality : (fun point => limit point * region.indicator test point) =
      (fun point => region.indicator limit point * test point) := by
    funext point
    by_cases inside : point ∈ region
    · rw [indicator_of_mem inside, indicator_of_mem inside]
    · rw [indicator_of_not_mem inside, indicator_of_not_mem inside, mul_zero, zero_mul]
  simpa only [sequenceEquality, limitEquality] using
    weak (region.indicator test) (testMember.indicator measurable)

theorem integrable_indicator_of_memLp_two
    {Domain : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {function : Domain → ℝ} {region : Set Domain}
    (member : MemLp function 2 measure) (measurable : MeasurableSet region)
    (finite : measure region ≠ ∞) : Integrable (region.indicator function) measure := by
  have constantMember : MemLp (region.indicator (fun _ => (1 : ℝ))) 2 measure :=
    memLp_indicator_const 2 measurable 1 (Or.inr finite)
  have productMember : MemLp ((region.indicator (fun _ => (1 : ℝ))) * function) 1 measure :=
    member.mul constantMember
  have equality : ((region.indicator (fun _ => (1 : ℝ))) * function) =
      region.indicator function := by
    funext point
    by_cases inside : point ∈ region <;> simp [inside]
  rw [equality] at productMember
  exact memLp_one_iff_integrable.mp productMember

end MeasureTheory
