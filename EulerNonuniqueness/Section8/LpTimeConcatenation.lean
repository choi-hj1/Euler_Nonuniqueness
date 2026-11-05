import EulerNonuniqueness.Section8.TimeConcatenation
import EulerNonuniqueness.Section8.CompactnessStatement

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem ContinuousInLpOn.timeConcatenation {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    {first second : ℝ} {exponent : ℝ≥0∞} {earlier later : ℝ → Plane → Value}
    (earlierContinuous : ContinuousInLpOn first exponent earlier)
    (laterContinuous : ContinuousInLpOn second exponent later)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (trace : earlier first =ᵐ[volume] later 0) :
    ContinuousInLpOn (first + second) exponent (EulerNonuniqueness.timeConcatenation first earlier later) := by
  obtain ⟨exponentBound, earlierMembers, earlierQuotientContinuous⟩ := earlierContinuous
  letI : Fact (1 ≤ exponent) := ⟨exponentBound⟩
  obtain ⟨_, laterMembers, laterQuotientContinuous⟩ := laterContinuous
  let earlierExtended : ℝ → Lp Value exponent volume := fun time =>
    (earlierMembers (projIcc 0 first firstNonnegative time)).toLp
      (earlier (projIcc 0 first firstNonnegative time))
  let laterExtended : ℝ → Lp Value exponent volume := fun time =>
    (laterMembers (projIcc 0 second secondNonnegative (time - first))).toLp
      (later (projIcc 0 second secondNonnegative (time - first)))
  have earlierExtendedContinuous : Continuous earlierExtended :=
    earlierQuotientContinuous.comp continuous_projIcc
  have laterExtendedContinuous : Continuous laterExtended :=
    laterQuotientContinuous.comp (continuous_projIcc.comp (continuous_id.sub continuous_const))
  have endpoint : earlierExtended first = laterExtended first := by
    dsimp only [earlierExtended, laterExtended]
    rw [projIcc_right, sub_self, projIcc_left]
    exact (earlierMembers ⟨first, firstNonnegative, le_rfl⟩).toLp_congr
      (laterMembers ⟨0, le_rfl, secondNonnegative⟩) trace
  have extendedContinuous : Continuous (fun time => if time ≤ first then earlierExtended time else laterExtended time) := by
    apply Continuous.if _ earlierExtendedContinuous laterExtendedContinuous
    intro time boundary
    have equal : time = first := by
      change time ∈ frontier (Iic first) at boundary
      simpa only [frontier_Iic, mem_singleton_iff] using boundary
    simpa only [equal] using endpoint
  let members : ∀ time : Icc 0 (first + second),
      MemLp (EulerNonuniqueness.timeConcatenation first earlier later time) exponent volume := by
    intro time
    by_cases inside : (time : ℝ) ≤ first
    · simpa only [EulerNonuniqueness.timeConcatenation, if_pos inside] using earlierMembers ⟨time, time.property.1, inside⟩
    · have shiftedInside : (time : ℝ) - first ∈ Icc 0 second := by
        constructor <;> linarith [time.property.2]
      simpa only [EulerNonuniqueness.timeConcatenation, if_neg inside] using laterMembers ⟨time - first, shiftedInside⟩
  refine ⟨exponentBound, members, ?_⟩
  apply (extendedContinuous.comp continuous_subtype_val).congr
  intro time
  change (if (time : ℝ) ≤ first then earlierExtended time else laterExtended time) =
    (members time).toLp (EulerNonuniqueness.timeConcatenation first earlier later time)
  by_cases inside : (time : ℝ) ≤ first
  · have timeInside : (time : ℝ) ∈ Icc 0 first := ⟨time.property.1, inside⟩
    simp only [if_pos inside, earlierExtended, projIcc_of_mem firstNonnegative timeInside]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun position => by simp only [EulerNonuniqueness.timeConcatenation, if_pos inside]
  · have shiftedInside : (time : ℝ) - first ∈ Icc 0 second := by
      constructor <;> linarith [time.property.2]
    simp only [if_neg inside, laterExtended, projIcc_of_mem secondNonnegative shiftedInside]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun position => by simp only [EulerNonuniqueness.timeConcatenation, if_neg inside]

end EulerNonuniqueness
