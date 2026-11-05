import EulerNonuniqueness.Section5.CascadeArbitraryWeightGeometry
import EulerNonuniqueness.Section5.CascadeCoMovingMonitors
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry

noncomputable section

open Filter

namespace EulerNonuniqueness.Paper

theorem ReferenceCentroidFieldGeometry.individual_center_distance
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {time : ℝ}
    {index : Fin count} (geometry : ReferenceCentroidFieldGeometry scales motion time index)
    (receiver : Fin 4) (source : Fin count) (patch : Fin 4)
    (different : (index, receiver) ≠ (source, patch)) :
    scales.individualInteractionDistance (index.val + 1) (source.val + 1) ≤
      ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖ := by
  by_cases same : source = index
  · subst source
    simp only [Scales.individualInteractionDistance, if_pos rfl, if_true]
    exact geometry.internalSeparated receiver patch (fun equality => different (by rw [equality]))
  · have valuesDifferent : source.val + 1 ≠ index.val + 1 :=
      fun equality => same (Fin.ext (Nat.add_right_cancel equality))
    simp only [Scales.individualInteractionDistance, if_neg valuesDifferent]
    exact geometry.centroidsSeparated receiver source (Finset.mem_erase.mpr ⟨same, Finset.mem_univ _⟩) patch

theorem Scales.eventually_weighted_comoving_center_ratios (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {weight factor parameterRadius : ℝ}
    (weightPositive : 0 < weight) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (parameterPositive : 0 < parameterRadius) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ centers : Fin count × Fin 4 → ℂ,
      let changed : Scales := {scales with frequency := frequency}
      (∀ receiver source, cascadeInternalGapMonitor changed factor receiver source centers ≤ 0) →
      (∀ label, cascadeExtentMonitor changed label centers ≤ 0) →
      (∀ receiver source, cascadeAnchorLowerMonitor changed receiver source centers ≤ 0) →
      ∀ receiver source, receiver ≠ source →
        let distance := (factor / 8) * changed.individualInteractionDistance
          (receiver.1.val + 1) (source.1.val + 1)
        2 * distance + 3 * changed.radius (source.1.val + 1) < ‖centers receiver - centers source‖ ∧
        2 * weight * changed.radius (receiver.1.val + 1) / distance ≤ 1 / 2 ∧
        96 * weight * changed.radius (receiver.1.val + 1) / ‖centers receiver - centers source‖ ≤ 1 / 2 ∧
        changed.radius (source.1.val + 1) / ‖centers receiver - centers source‖ ≤ parameterRadius := by
  filter_upwards [scales.eventually_weighted_actual_center_ratios amplitudePositive ratioBound alphaPositive
      weightPositive factorPositive parameterPositive,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)] with frequency ratios geometry
  intro count centers
  dsimp only
  intro internal extent separated receiver source different
  let changed : Scales := {scales with frequency := frequency}
  have clearance := cascade_comoving_clearance_of_nonpositive_monitors changed centers factorPositive factorSmall
    internal extent separated (fun index => (geometry (index.val + 1)).2.2.1)
    (fun index => (geometry (index.val + 1)).2.1) (fun index => (geometry (index.val + 1)).2.2.2)
    receiver source different
  have nonnegative : 0 ≤ 3 * changed.radius (source.1.val + 1) := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have lower : (factor / 4) * changed.individualInteractionDistance
      (receiver.1.val + 1) (source.1.val + 1) ≤ ‖centers receiver - centers source‖ := by linarith [clearance.2]
  have bounds := ratios (receiver.1.val + 1) (source.1.val + 1) (centers receiver) (centers source) lower
  refine ⟨?_, bounds⟩
  dsimp only
  nlinarith only [clearance.2]

theorem Scales.eventually_weighted_reference_center_ratios (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {weight factor parameterRadius : ℝ}
    (weightPositive : 0 < weight) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (parameterPositive : 0 < parameterRadius) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ motion : PatchMotion count, ∀ time : ℝ,
      let changed : Scales := {scales with frequency := frequency}
      ∀ index : Fin count, ReferenceCentroidFieldGeometry changed motion time index →
      ∀ receiver : Fin 4, ∀ source : Fin count, ∀ patch : Fin 4,
      (index, receiver) ≠ (source, patch) →
      let displacement := ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖
      2 * weight * changed.radius (index.val + 1) /
          ((factor / 8) * changed.individualInteractionDistance (index.val + 1) (source.val + 1)) ≤ 1 / 2 ∧
      96 * weight * changed.radius (index.val + 1) / displacement ≤ 1 / 2 ∧
      changed.radius (source.val + 1) / displacement ≤ parameterRadius := by
  filter_upwards [scales.eventually_weighted_actual_center_ratios amplitudePositive ratioBound alphaPositive
    weightPositive factorPositive parameterPositive] with frequency ratios
  intro count motion time
  dsimp only
  intro index geometry receiver source patch different
  have lower := geometry.individual_center_distance receiver source patch different
  have positive := ({scales with frequency := frequency} : Scales).individualInteractionDistance_pos
    (index.val + 1) (source.val + 1)
  have weak : (factor / 4) * ({scales with frequency := frequency} : Scales).individualInteractionDistance
      (index.val + 1) (source.val + 1) ≤
      ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖ := by
    have multiplied := mul_le_mul_of_nonneg_right factorSmall positive.le
    nlinarith
  exact ratios (index.val + 1) (source.val + 1) _ _ weak

end EulerNonuniqueness.Paper
