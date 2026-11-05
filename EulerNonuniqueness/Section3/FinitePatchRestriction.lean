import EulerNonuniqueness.Section4.ReferenceStatement
import EulerNonuniqueness.Section8.Restriction

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.mono {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {horizon smaller : ℝ} (evolution : FinitePatchEvolution scales motion horizon) (ordered : smaller ≤ horizon) :
    FinitePatchEvolution scales motion smaller := by
  have intervalSubset : Icc (0 : ℝ) smaller ⊆ Icc 0 horizon := Icc_subset_Icc_right ordered
  refine ⟨evolution.1.mono ordered, fun index patch => (evolution.2.1 index patch).mono ordered, ?_, ?_, ?_, ?_⟩
  · intro time inside
    exact ⟨(evolution.2.2.1 time (intervalSubset inside)).1,
      (evolution.2.2.1 time (intervalSubset inside)).2.mono_left (nhdsWithin_mono time intervalSubset)⟩
  · intro time inside
    exact evolution.2.2.2.1 time (intervalSubset inside)
  · intro index patch angle
    exact (evolution.2.2.2.2.1 index patch angle).mono intervalSubset
  · intro index patch angle time inside
    exact evolution.2.2.2.2.2 index patch angle time ⟨inside.1, inside.2.trans_le ordered⟩

end EulerNonuniqueness.Paper
