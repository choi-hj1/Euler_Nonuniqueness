import EulerNonuniqueness.Section5.CascadeCoMovingClearance

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper

def cascadeBlockCenter {count : ℕ} (centers : Fin count × Fin 4 → ℂ) (index : Fin count) : ℂ :=
  (∑ patch : Fin 4, centers (index, patch)) / 4

def cascadeExtentMonitor {count : ℕ} (scales : Scales) (label : Fin count × Fin 4)
    (centers : Fin count × Fin 4 → ℂ) : ℝ :=
  ‖centers label - cascadeBlockCenter centers label.1‖ - scales.location (label.1.val + 1) / 100

def cascadeAnchorLowerMonitor {count : ℕ} (scales : Scales) (first second : Fin count)
    (centers : Fin count × Fin 4 → ℂ) : ℝ :=
  if first = second then -1 else
    |scales.location (first.val + 1) - scales.location (second.val + 1)| / 2 -
      ‖cascadeBlockCenter centers first - cascadeBlockCenter centers second‖

def cascadeAnchorUpperMonitor {count : ℕ} (scales : Scales) (first second : Fin count)
    (centers : Fin count × Fin 4 → ℂ) : ℝ :=
  if first = second then -1 else
    ‖cascadeBlockCenter centers first - cascadeBlockCenter centers second‖ -
      2 * |scales.location (first.val + 1) - scales.location (second.val + 1)|

def cascadeAnchorNormMonitor {count : ℕ} (index : Fin count) (centers : Fin count × Fin 4 → ℂ) : ℝ :=
  ‖cascadeBlockCenter centers index‖ - 3

theorem cascadeBlockCenter_continuous {count : ℕ} (index : Fin count) :
    Continuous (fun centers : Fin count × Fin 4 → ℂ => cascadeBlockCenter centers index) :=
  (continuous_finset_sum Finset.univ (fun patch _ => continuous_apply (index, patch))).div_const 4

theorem cascadeExtentMonitor_continuous {count : ℕ} (scales : Scales) (label : Fin count × Fin 4) :
    Continuous (cascadeExtentMonitor scales label) :=
  ((continuous_apply label).sub (cascadeBlockCenter_continuous label.1)).norm.sub continuous_const

theorem cascadeAnchorLowerMonitor_continuous {count : ℕ} (scales : Scales) (first second : Fin count) :
    Continuous (cascadeAnchorLowerMonitor scales first second) := by
  unfold cascadeAnchorLowerMonitor
  split_ifs
  · exact continuous_const
  · exact continuous_const.sub ((cascadeBlockCenter_continuous first).sub (cascadeBlockCenter_continuous second)).norm

theorem cascadeAnchorUpperMonitor_continuous {count : ℕ} (scales : Scales) (first second : Fin count) :
    Continuous (cascadeAnchorUpperMonitor scales first second) := by
  unfold cascadeAnchorUpperMonitor
  split_ifs
  · exact continuous_const
  · exact ((cascadeBlockCenter_continuous first).sub (cascadeBlockCenter_continuous second)).norm.sub continuous_const

theorem cascadeAnchorNormMonitor_continuous {count : ℕ} (index : Fin count) :
    Continuous (cascadeAnchorNormMonitor (count := count) index) :=
  (cascadeBlockCenter_continuous index).norm.sub continuous_const

theorem cascade_comoving_clearance_of_nonpositive_monitors {count : ℕ}
    (scales : Scales) (centers : Fin count × Fin 4 → ℂ) {factor : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ receiver source, cascadeInternalGapMonitor scales factor receiver source centers ≤ 0)
    (extent : ∀ label, cascadeExtentMonitor scales label centers ≤ 0)
    (separation : ∀ receiver source, cascadeAnchorLowerMonitor scales receiver source centers ≤ 0)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (receiver source : Fin count × Fin 4) (different : receiver ≠ source) :
    factor * scales.length (receiver.1.val + 1) / 400 + 3 * scales.radius (source.1.val + 1) <
        ‖centers receiver - centers source‖ ∧
    (factor / 4) * scales.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) +
      3 * scales.radius (source.1.val + 1) < ‖centers receiver - centers source‖ := by
  apply cascade_comoving_center_clearance scales centers (cascadeBlockCenter centers) factorPositive factorSmall
    ?_ (fun label => sub_nonpos.mp (extent label)) ?_ lengthSmall radiusInternal radiusLocation receiver source different
  · intro index first second different
    have estimate := internal (index, first) (index, second)
    have condition : (index, first).1 = (index, second).1 ∧ (index, first).2 ≠ (index, second).2 := ⟨rfl, different⟩
    rw [cascadeInternalGapMonitor, if_pos condition] at estimate
    exact sub_nonpos.mp estimate
  · intro receiver source different
    have estimate := separation receiver source
    rw [cascadeAnchorLowerMonitor, if_neg different] at estimate
    exact sub_nonpos.mp estimate

theorem cascadeBlockCenter_eq_of_pair_sums {count : ℕ} (centers : Fin count × Fin 4 → ℂ)
    (index : Fin count) (center : ℂ)
    (positive : centers (index, 0) + centers (index, 1) = 2 * center)
    (negative : centers (index, 2) + centers (index, 3) = 2 * center) :
    cascadeBlockCenter centers index = center := by
  have identity : (∑ patch : Fin 4, centers (index, patch)) =
      (centers (index, 0) + centers (index, 1)) + (centers (index, 2) + centers (index, 3)) := by
    simp [Fin.sum_univ_succ]
    ring
  rw [cascadeBlockCenter, identity, positive, negative]
  ring

end EulerNonuniqueness.Paper
