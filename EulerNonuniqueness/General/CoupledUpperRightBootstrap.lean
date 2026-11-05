import EulerNonuniqueness.General.UpperRightBootstrap
import Mathlib.Topology.Order.Lattice

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem two_curve_norm_bootstrap_of_upper_right_slopes
    {first : ℝ → Space} {second : ℝ → Target}
    {terminal firstRadius secondRadius firstRate secondRate : ℝ}
    (terminalNonnegative : 0 ≤ terminal)
    (firstContinuous : ContinuousOn first (Icc 0 terminal))
    (secondContinuous : ContinuousOn second (Icc 0 terminal))
    (firstRateNonnegative : 0 ≤ firstRate) (secondRateNonnegative : 0 ≤ secondRate)
    (firstBudget : ‖first 0‖ + firstRate * terminal < firstRadius)
    (secondBudget : ‖second 0‖ + secondRate * terminal < secondRadius)
    (firstSlopes : ∀ base ∈ Ico 0 terminal,
      (∀ current ∈ Icc 0 base, ‖first current‖ ≤ firstRadius ∧ ‖second current‖ ≤ secondRadius) →
      ∀ threshold, firstRate < threshold →
        ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖first current‖) base later < threshold)
    (secondSlopes : ∀ base ∈ Ico 0 terminal,
      (∀ current ∈ Icc 0 base, ‖first current‖ ≤ firstRadius ∧ ‖second current‖ ≤ secondRadius) →
      ∀ threshold, secondRate < threshold →
        ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖second current‖) base later < threshold) :
    ∀ time ∈ Icc 0 terminal,
      ‖first time‖ ≤ ‖first 0‖ + firstRate * time ∧
      ‖second time‖ ≤ ‖second 0‖ + secondRate * time := by
  have firstInitial : ‖first 0‖ ≤ firstRadius := by
    have travel := mul_nonneg firstRateNonnegative terminalNonnegative
    linarith
  have secondInitial : ‖second 0‖ ≤ secondRadius := by
    have travel := mul_nonneg secondRateNonnegative terminalNonnegative
    linarith
  have confined : ∀ time ∈ Icc 0 terminal,
      ‖first time‖ ≤ firstRadius ∧ ‖second time‖ ≤ secondRadius := by
    intro time inside
    by_contra failure
    have positive : 0 < max (‖first time‖ - firstRadius) (‖second time‖ - secondRadius) := by
      by_contra notPositive
      have bound := le_of_not_gt notPositive
      have components := max_le_iff.mp bound
      exact failure ⟨by linarith [components.1], by linarith [components.2]⟩
    have continuous : ContinuousOn
        (fun current => max (‖first current‖ - firstRadius) (‖second current‖ - secondRadius)) (Icc 0 time) :=
      ((firstContinuous.mono (Icc_subset_Icc le_rfl inside.2)).norm.sub continuous_const.continuousOn).sup
        ((secondContinuous.mono (Icc_subset_Icc le_rfl inside.2)).norm.sub continuous_const.continuousOn)
    have initial : max (‖first 0‖ - firstRadius) (‖second 0‖ - secondRadius) ≤ 0 :=
      max_le (sub_nonpos.mpr firstInitial) (sub_nonpos.mpr secondInitial)
    obtain ⟨contact, contactInside, contactValue, strictBefore⟩ :=
      exists_first_zero_of_initial_nonpos_of_positive inside.1 continuous initial positive
    have history (base : ℝ) (baseInside : base ∈ Ico 0 contact) :
        ∀ current ∈ Icc 0 base, ‖first current‖ ≤ firstRadius ∧ ‖second current‖ ≤ secondRadius := by
      intro current currentInside
      have negative := strictBefore current currentInside.1 (currentInside.2.trans_lt baseInside.2)
      have components := max_lt_iff.mp negative
      exact ⟨(sub_neg.mp components.1).le, (sub_neg.mp components.2).le⟩
    have firstBound := norm_le_linear_of_upper_right_slopes
      (firstContinuous.mono (Icc_subset_Icc le_rfl (contactInside.2.trans inside.2)))
      (by
        intro base baseInside threshold strict
        exact firstSlopes base ⟨baseInside.1, baseInside.2.trans_le (contactInside.2.trans inside.2)⟩
          (history base baseInside) threshold strict)
      contact ⟨contactInside.1, le_rfl⟩
    have secondBound := norm_le_linear_of_upper_right_slopes
      (secondContinuous.mono (Icc_subset_Icc le_rfl (contactInside.2.trans inside.2)))
      (by
        intro base baseInside threshold strict
        exact secondSlopes base ⟨baseInside.1, baseInside.2.trans_le (contactInside.2.trans inside.2)⟩
          (history base baseInside) threshold strict)
      contact ⟨contactInside.1, le_rfl⟩
    have firstTravel := mul_le_mul_of_nonneg_left (contactInside.2.trans inside.2) firstRateNonnegative
    have secondTravel := mul_le_mul_of_nonneg_left (contactInside.2.trans inside.2) secondRateNonnegative
    have firstStrict : ‖first contact‖ - firstRadius < 0 := by linarith
    have secondStrict : ‖second contact‖ - secondRadius < 0 := by linarith
    have contactNegative := max_lt firstStrict secondStrict
    linarith
  have firstBound := norm_le_linear_of_upper_right_slopes firstContinuous
    (by
      intro base inside threshold strict
      exact firstSlopes base inside
        (fun current currentInside => confined current ⟨currentInside.1, currentInside.2.trans inside.2.le⟩)
        threshold strict)
  have secondBound := norm_le_linear_of_upper_right_slopes secondContinuous
    (by
      intro base inside threshold strict
      exact secondSlopes base inside
        (fun current currentInside => confined current ⟨currentInside.1, currentInside.2.trans inside.2.le⟩)
        threshold strict)
  exact fun time inside => ⟨firstBound time inside, secondBound time inside⟩

end EulerNonuniqueness.General
