import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section

open Set

namespace EulerNonuniqueness

theorem exists_quantitative_first_contact
    {actual model modelDerivative : ℝ → ℝ}
    {initial center halfWidth level slope error : ℝ}
    (halfWidthPositive : 0 < halfWidth) (initialBefore : initial ≤ center - halfWidth)
    (slopePositive : 0 < slope) (errorNonnegative : 0 ≤ error)
    (errorSmall : error < slope * halfWidth)
    (actualContinuous : ContinuousOn actual (Icc initial (center + halfWidth)))
    (modelContinuous : ContinuousOn model (Icc initial (center + halfWidth)))
    (modelAtCenter : model center = level)
    (modelHasDerivative : ∀ time ∈ Ioo (center - halfWidth) (center + halfWidth),
      HasDerivAt model (modelDerivative time) time)
    (derivativeLower : ∀ time ∈ Ioo (center - halfWidth) (center + halfWidth),
      slope ≤ modelDerivative time)
    (earlierMargin : ∀ time ∈ Icc initial (center - halfWidth), model time ≤ level - slope * halfWidth)
    (close : ∀ time ∈ Icc initial (center + halfWidth), |actual time - model time| ≤ error) :
    ∃ contact ∈ Icc (center - halfWidth) (center + halfWidth),
      actual contact = level ∧
      (∀ time ∈ Ico initial contact, actual time < level) ∧
      |contact - center| ≤ error / slope := by
  have localInside : Icc (center - halfWidth) (center + halfWidth) ⊆
      Icc initial (center + halfWidth) := Icc_subset_Icc initialBefore le_rfl
  have modelGrowth {first second : ℝ}
      (firstInside : first ∈ Icc (center - halfWidth) (center + halfWidth))
      (secondInside : second ∈ Icc (center - halfWidth) (center + halfWidth))
      (ordered : first ≤ second) : slope * (second - first) ≤ model second - model first := by
    rcases eq_or_lt_of_le ordered with equal | strict
    · subst second
      simp only [sub_self, mul_zero, le_refl]
    have segmentInside : Icc first second ⊆ Icc initial (center + halfWidth) :=
      Icc_subset_Icc (initialBefore.trans firstInside.1) secondInside.2
    have interiorInside : Ioo first second ⊆ Ioo (center - halfWidth) (center + halfWidth) :=
      fun time member => ⟨firstInside.1.trans_lt member.1, member.2.trans_le secondInside.2⟩
    obtain ⟨time, timeInside, derivativeSlope⟩ := exists_hasDerivAt_eq_slope model modelDerivative strict
      (modelContinuous.mono segmentInside) (fun time member => modelHasDerivative time (interiorInside member))
    have lower : slope ≤ (model second - model first) / (second - first) :=
      (derivativeLower time (interiorInside timeInside)).trans_eq derivativeSlope
    exact (le_div_iff₀ (sub_pos.mpr strict)).mp lower
  have centerInside : center ∈ Icc (center - halfWidth) (center + halfWidth) := by
    constructor <;> linarith only [halfWidthPositive]
  have upperInside : center + halfWidth ∈ Icc (center - halfWidth) (center + halfWidth) := by
    constructor <;> linarith only [halfWidthPositive]
  have earlierNegative (time : ℝ) (member : time ∈ Icc initial (center - halfWidth)) : actual time < level := by
    have margin := earlierMargin time member
    have approximation := (abs_le.mp (close time ⟨member.1, by linarith only [member.2, halfWidthPositive]⟩)).2
    linarith only [margin, approximation, errorSmall]
  have initialNegative : actual initial < level := earlierNegative initial ⟨le_rfl, initialBefore⟩
  have upperPositive : level < actual (center + halfWidth) := by
    have growth := modelGrowth centerInside upperInside centerInside.2
    have approximation := (abs_le.mp (close (center + halfWidth) (localInside upperInside))).1
    rw [modelAtCenter] at growth
    nlinarith only [growth, approximation, errorSmall]
  have intervalOrder : initial ≤ center + halfWidth := (localInside centerInside).1.trans centerInside.2
  obtain ⟨root, rootInside, rootValue⟩ := intermediate_value_Icc intervalOrder actualContinuous
    (show level ∈ Icc (actual initial) (actual (center + halfWidth)) from
      ⟨initialNegative.le, upperPositive.le⟩)
  have rootsClosed : IsClosed (Icc initial (center + halfWidth) ∩ actual ⁻¹' {level}) :=
    actualContinuous.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have rootsCompact : IsCompact (Icc initial (center + halfWidth) ∩ actual ⁻¹' {level}) :=
    isCompact_Icc.of_isClosed_subset rootsClosed inter_subset_left
  obtain ⟨contact, least⟩ := rootsCompact.exists_isLeast ⟨root, rootInside, rootValue⟩
  have contactGlobal : contact ∈ Icc initial (center + halfWidth) := least.1.1
  have contactValue : actual contact = level := least.1.2
  have contactAfter : center - halfWidth < contact := by
    by_contra failure
    have negative := earlierNegative contact ⟨contactGlobal.1, le_of_not_gt failure⟩
    linarith only [negative, contactValue]
  have contactLocal : contact ∈ Icc (center - halfWidth) (center + halfWidth) :=
    ⟨contactAfter.le, contactGlobal.2⟩
  refine ⟨contact, contactLocal, contactValue, ?_, ?_⟩
  · intro time member
    by_contra failure
    have timeBound : time ≤ center + halfWidth := member.2.le.trans contactGlobal.2
    obtain ⟨earlierRoot, earlierInside, earlierValue⟩ := intermediate_value_Icc member.1
      (actualContinuous.mono (Icc_subset_Icc le_rfl timeBound))
      (show level ∈ Icc (actual initial) (actual time) from ⟨initialNegative.le, le_of_not_gt failure⟩)
    have minimal : contact ≤ earlierRoot := least.2
      ⟨⟨earlierInside.1, earlierInside.2.trans timeBound⟩, earlierValue⟩
    linarith only [minimal, earlierInside.2, member.2]
  · have approximation := abs_le.mp (close contact contactGlobal)
    rw [contactValue] at approximation
    have quotientNonnegative : 0 ≤ error / slope := div_nonneg errorNonnegative slopePositive.le
    apply abs_le.mpr
    rcases le_total contact center with before | after
    · have growth := modelGrowth contactLocal centerInside before
      rw [modelAtCenter] at growth
      refine ⟨?_, (sub_nonpos.mpr before).trans quotientNonnegative⟩
      have distanceBound : center - contact ≤ error / slope := by
        apply (le_div_iff₀ slopePositive).mpr
        nlinarith only [growth, approximation.2]
      linarith only [distanceBound]
    · have growth := modelGrowth centerInside contactLocal after
      rw [modelAtCenter] at growth
      refine ⟨(neg_nonpos.mpr quotientNonnegative).trans (sub_nonneg.mpr after), ?_⟩
      apply (le_div_iff₀ slopePositive).mpr
      nlinarith only [growth, approximation.1]

end EulerNonuniqueness
