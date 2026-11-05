import EulerNonuniqueness.Section5.CascadeCoMovingMonitors
import EulerNonuniqueness.Section5.CascadeInitialGeometry
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem cascadeBlockCenter_initial {count : ℕ} (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (phase unstable : Fin count → ℝ) (dipoleAngle : ℝ)
    (index : Fin count) :
    cascadeBlockCenter (cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle) index =
      (scales.location (index.val + 1) : ℂ) := by
  apply cascadeBlockCenter_eq_of_pair_sums
  · by_cases terminal : index.val + 1 = count
    · simp [cascadeInitialCenter, terminal, separatingInitialCenter]
      <;> ring
    · simp [cascadeInitialCenter, terminal, initialDiskCenter]
      <;> ring
  · by_cases terminal : index.val + 1 = count
    · simp [cascadeInitialCenter, terminal, separatingInitialCenter]
      <;> ring
    · simp [cascadeInitialCenter, terminal, initialDiskCenter]
      <;> ring

theorem cascadeExtentMonitor_initial_of_offset {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (phase unstable : Fin count → ℝ)
    (dipoleAngle : ℝ) (label : Fin count × Fin 4)
    (offset : ‖cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle label -
      (scales.location (label.1.val + 1) : ℂ)‖ < scales.location (label.1.val + 1) / 100) :
    cascadeExtentMonitor scales label
      (cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle) < 0 := by
  unfold cascadeExtentMonitor
  rw [cascadeBlockCenter_initial]
  exact sub_neg.mpr offset

theorem cascadeAnchorMonitors_initial_strict {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (phase unstable : Fin count → ℝ)
    (dipoleAngle : ℝ) :
    (∀ first second, cascadeAnchorLowerMonitor scales first second
      (cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle) < 0) ∧
    (∀ first second, cascadeAnchorUpperMonitor scales first second
      (cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle) < 0) ∧
    (∀ index, cascadeAnchorNormMonitor index
      (cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle) < 0) := by
  have distance (first second : Fin count) :
      ‖(scales.location (first.val + 1) : ℂ) - (scales.location (second.val + 1) : ℂ)‖ =
        |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have positive (first second : Fin count) (different : first ≠ second) :
      0 < |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
    apply scales.location_distance_pos
    intro equal
    apply different
    apply Fin.ext
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro first second
    by_cases same : first = second
    · simp [cascadeAnchorLowerMonitor, same]
    · simp only [cascadeAnchorLowerMonitor, if_neg same, cascadeBlockCenter_initial, distance]
      linarith [positive first second same]
  · intro first second
    by_cases same : first = second
    · simp [cascadeAnchorUpperMonitor, same]
    · simp only [cascadeAnchorUpperMonitor, if_neg same, cascadeBlockCenter_initial, distance]
      linarith [positive first second same]
  · intro index
    simp only [cascadeAnchorNormMonitor, cascadeBlockCenter_initial, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (scales.location_pos _)]
    linarith [scales.location_le_one (index.val + 1)]

end EulerNonuniqueness.Paper
