import EulerNonuniqueness.Section3.PeriodicHilbertC1

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance translationHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance translationC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem min_le_sqrt_mul_sqrt {first second : ℝ} (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) :
    min first second ≤ Real.sqrt first * Real.sqrt second := by
  rcases le_total first second with ordered | ordered
  · rw [min_eq_left ordered]
    calc
      first = Real.sqrt first * Real.sqrt first := (Real.mul_self_sqrt firstNonnegative).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ordered) (Real.sqrt_nonneg _)
  · rw [min_eq_right ordered]
    calc
      second = Real.sqrt second * Real.sqrt second := (Real.mul_self_sqrt secondNonnegative).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ordered) (Real.sqrt_nonneg _)

theorem c1ValueHolder_shift_difference_holder (data : PeriodicC1HolderHalf)
    (firstShift secondShift first second : ℝ) :
    ‖((holderLabelShift firstShift (c1ValueHolder data)).val.1 first -
        (holderLabelShift secondShift (c1ValueHolder data)).val.1 first) -
      ((holderLabelShift firstShift (c1ValueHolder data)).val.1 second -
        (holderLabelShift secondShift (c1ValueHolder data)).val.1 second)‖ ≤
      (2 * ‖data‖ * Real.sqrt |firstShift - secondShift|) * Real.sqrt |first - second| := by
  let difference :=
    (data.val.1 (first + firstShift) - data.val.1 (first + secondShift)) -
      (data.val.1 (second + firstShift) - data.val.1 (second + secondShift))
  have shiftBound : ‖difference‖ ≤ 2 * ‖data‖ * |firstShift - secondShift| := by
    apply (norm_sub_le _ _).trans
    have firstBound := PeriodicC1HolderHalf.lipschitz_bound data
      (first + firstShift) (first + secondShift)
    have secondBound := PeriodicC1HolderHalf.lipschitz_bound data
      (second + firstShift) (second + secondShift)
    simp only [add_sub_add_left_eq_sub] at firstBound secondBound
    linarith
  have spatialBound : ‖difference‖ ≤ 2 * ‖data‖ * |first - second| := by
    have identity : difference =
        (data.val.1 (first + firstShift) - data.val.1 (second + firstShift)) -
          (data.val.1 (first + secondShift) - data.val.1 (second + secondShift)) := by
      dsimp only [difference]
      abel
    rw [identity]
    apply (norm_sub_le _ _).trans
    have firstBound := PeriodicC1HolderHalf.lipschitz_bound data
      (first + firstShift) (second + firstShift)
    have secondBound := PeriodicC1HolderHalf.lipschitz_bound data
      (first + secondShift) (second + secondShift)
    simp only [add_sub_add_right_eq_sub] at firstBound secondBound
    linarith
  have estimate : ‖difference‖ ≤ 2 * ‖data‖ * min |firstShift - secondShift| |first - second| := by
    rcases le_total |firstShift - secondShift| |first - second| with ordered | ordered
    · simpa only [min_eq_left ordered] using shiftBound
    · simpa only [min_eq_right ordered] using spatialBound
  exact estimate.trans ((mul_le_mul_of_nonneg_left
    (min_le_sqrt_mul_sqrt (abs_nonneg _) (abs_nonneg _)) (by positivity)).trans_eq (by ring))

theorem c1ValueHolder_shift_difference_norm (data : PeriodicC1HolderHalf)
    {firstShift secondShift : ℝ} (nearby : |firstShift - secondShift| ≤ 1) :
    ‖holderLabelShift firstShift (c1ValueHolder data) -
      holderLabelShift secondShift (c1ValueHolder data)‖ ≤
      2 * ‖data‖ * Real.sqrt |firstShift - secondShift| := by
  apply PeriodicHolderHalf.norm_le_of_bounds _ (by positivity)
  · intro label
    have estimate := PeriodicC1HolderHalf.lipschitz_bound data
      (label + firstShift) (label + secondShift)
    simp only [add_sub_add_left_eq_sub] at estimate
    have root := Real.sqrt_nonneg |firstShift - secondShift|
    have square := Real.sq_sqrt (abs_nonneg (firstShift - secondShift))
    have rootSmall := Real.sqrt_le_sqrt nearby
    norm_num only [Real.sqrt_one] at rootSmall
    have distanceBound : |firstShift - secondShift| ≤ Real.sqrt |firstShift - secondShift| := by
      nlinarith
    exact estimate.trans ((mul_le_mul_of_nonneg_left distanceBound (norm_nonneg data)).trans
      (by nlinarith [mul_nonneg (norm_nonneg data) root]))
  · exact c1ValueHolder_shift_difference_holder data firstShift secondShift

theorem continuous_c1ValueHolder_shift (data : PeriodicC1HolderHalf) :
    Continuous (fun offset => holderLabelShift offset (c1ValueHolder data)) := by
  apply continuous_iff_continuousAt.mpr
  intro offset
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have nearby : ∀ᶠ current in 𝓝 offset, |current - offset| ≤ 1 := by
    have actual := (isOpen_Ioo.mem_nhds (show offset ∈ Ioo (offset - 1) (offset + 1) by
      constructor <;> linarith))
    filter_upwards [actual] with current inside
    rw [abs_le]
    constructor <;> linarith [inside.1, inside.2]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (nearby.mono (fun _ inside => c1ValueHolder_shift_difference_norm data inside))
  have continuous : Continuous (fun current : ℝ =>
      2 * ‖data‖ * Real.sqrt |current - offset|) :=
    continuous_const.mul ((continuous_id.sub continuous_const).abs.sqrt)
  have limit := continuous.tendsto offset
  simpa only [sub_self, abs_zero, Real.sqrt_zero, mul_zero] using limit

end

end EulerNonuniqueness.Paper
