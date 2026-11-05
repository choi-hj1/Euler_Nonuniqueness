import EulerNonuniqueness.Section5.CascadeCenterClearance

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

def cascadeInternalGapMonitor {count : ℕ} (scales : Scales) (factor : ℝ)
    (receiver source : Fin count × Fin 4) (centers : Fin count × Fin 4 → ℂ) : ℝ :=
  if receiver.1 = source.1 ∧ receiver.2 ≠ source.2 then
    factor * scales.length (receiver.1.val + 1) - ‖centers receiver - centers source‖
  else -1

def cascadeLocationMonitor {count : ℕ} (scales : Scales)
    (label : Fin count × Fin 4) (centers : Fin count × Fin 4 → ℂ) : ℝ :=
  ‖centers label - (scales.location (label.1.val + 1) : ℂ)‖ - scales.location (label.1.val + 1) / 100

theorem cascadeInternalGapMonitor_continuous {count : ℕ} (scales : Scales) (factor : ℝ)
    (receiver source : Fin count × Fin 4) : Continuous (cascadeInternalGapMonitor scales factor receiver source) := by
  unfold cascadeInternalGapMonitor
  split_ifs
  · exact continuous_const.sub ((continuous_apply receiver).sub (continuous_apply source)).norm
  · exact continuous_const

theorem cascadeLocationMonitor_continuous {count : ℕ} (scales : Scales)
    (label : Fin count × Fin 4) : Continuous (cascadeLocationMonitor scales label) :=
  ((continuous_apply label).sub continuous_const).norm.sub continuous_const

theorem cascade_center_clearance_of_nonpositive_monitors {count : ℕ}
    (scales : Scales) (centers : Fin count × Fin 4 → ℂ) (factor : ℝ)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ receiver source, cascadeInternalGapMonitor scales factor receiver source centers ≤ 0)
    (offset : ∀ label, cascadeLocationMonitor scales label centers ≤ 0)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusInternal : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (receiver source : Fin count × Fin 4) (different : receiver ≠ source) :
    factor * scales.length (receiver.1.val + 1) / 400 + 3 * scales.radius (source.1.val + 1) <
        ‖centers receiver - centers source‖ ∧
    (factor / 4) * scales.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) +
      3 * scales.radius (source.1.val + 1) < ‖centers receiver - centers source‖ := by
  apply cascade_center_clearance_of_internal_gap_and_location_control scales centers factor factorPositive factorSmall
    ?_ ?_ lengthSmall radiusInternal radiusLocation receiver source different
  · intro index first second different
    have estimate := internal (index, first) (index, second)
    have condition : (index, first).1 = (index, second).1 ∧
        (index, first).2 ≠ (index, second).2 := ⟨rfl, different⟩
    rw [cascadeInternalGapMonitor, if_pos condition] at estimate
    exact sub_nonpos.mp estimate
  · intro label
    exact sub_nonpos.mp (offset label)

theorem cascadeLocationMonitor_initial_strict {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (phase unstable : Fin count → ℝ)
    (dipoleAngle bound : ℝ) (referenceSmall : ∀ index, |unstable index| ≤ 1 / 2)
    (referenceBound : 3 ≤ bound)
    (positiveBound : ‖orbit.positive sectionTime‖ ≤ bound)
    (negativeBound : ‖orbit.negative sectionTime‖ ≤ bound)
    (lengthSmall : ∀ index : Fin count,
      bound * scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 200)
    (label : Fin count × Fin 4) :
    cascadeLocationMonitor scales label
      (cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle) < 0 := by
  have estimate := cascadeInitialCenter_offset_bound scales orbit sectionTime phase unstable dipoleAngle bound
    referenceSmall referenceBound positiveBound negativeBound label
  unfold cascadeLocationMonitor
  linarith [lengthSmall label.1, scales.location_pos (label.1.val + 1)]

theorem cascadeInternalGapMonitor_initial_strict {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (phase unstable : Fin count → ℝ)
    (dipoleAngle factor : ℝ) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (referenceSmall : ∀ index, |unstable index| ≤ 1 / 2)
    (positiveGap : 2 * factor ≤ 2 * ‖orbit.positive sectionTime‖)
    (negativeGap : 2 * factor ≤ 2 * ‖orbit.negative sectionTime‖)
    (differenceGap : 2 * factor ≤ ‖orbit.positive sectionTime - orbit.negative sectionTime‖)
    (sumGap : 2 * factor ≤ ‖orbit.positive sectionTime + orbit.negative sectionTime‖)
    (receiver source : Fin count × Fin 4) :
    cascadeInternalGapMonitor scales factor receiver source
      (cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle) < 0 := by
  unfold cascadeInternalGapMonitor
  split_ifs with active
  · rcases receiver with ⟨receiver, first⟩
    rcases source with ⟨source, second⟩
    obtain ⟨same, different⟩ := active
    dsimp only [Prod.fst, Prod.snd] at same different ⊢
    subst source
    have lower : 2 * factor * scales.length (receiver.val + 1) ≤
        ‖cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle (receiver, first) -
          cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle (receiver, second)‖ := by
      unfold cascadeInitialCenter
      simp only [Prod.fst, Prod.snd]
      split_ifs with last
      · simpa only [last, mul_comm] using separatingInitialCenter_pair_lower scales orbit sectionTime
          dipoleAngle (2 * factor) positiveGap negativeGap differenceGap sumGap
          (receiver.val + 1) first second different
      · have estimate := initialDiskCenter_same_scale_separation scales (receiver.val + 1)
          (phase receiver) (unstable receiver) (referenceSmall receiver) first second different
        nlinarith [scales.length_pos (receiver.val + 1)]
    nlinarith [mul_pos factorPositive (scales.length_pos (receiver.val + 1))]
  · norm_num

end EulerNonuniqueness.Paper
