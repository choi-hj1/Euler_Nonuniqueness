import EulerNonuniqueness.Section6.MovingPatchSourceRelativeSeries

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

structure MovingPatchFamilySourceComparison (count : ℕ) where
  first : FiniteMovingPatchFamily count
  second : FiniteMovingPatchFamily count
  densityEqual : ∀ source, first.density source = second.density source
  firstReceiver : ℝ → ℂ
  secondReceiver : ℝ → ℂ
  receiverRadius : ℝ
  receiverRadius_nonnegative : 0 ≤ receiverRadius
  time : ℝ
  initial : Fin count → PeriodicC1HolderHalf
  final : Fin count → PeriodicC1HolderHalf
  firstShape : ∀ source, (first.patch source).shape time = diskPhysicalSpectralChart (initial source)
  secondShape : ∀ source, (second.patch source).shape time = diskPhysicalSpectralChart (final source)
  radiusEqual : ∀ source, (first.patch source).radius = (second.patch source).radius
  phaseEqual : ∀ source, (first.patch source).phase time = (second.patch source).phase time
  firstArea : ∀ source, volume.real ((first.patch source).domain time) = Real.pi * (first.patch source).radius ^ 2
  secondArea : ∀ source, volume.real ((second.patch source).domain time) = Real.pi * (second.patch source).radius ^ 2

namespace MovingPatchFamilySourceComparison

def source {count : ℕ} (comparison : MovingPatchFamilySourceComparison count) (index : Fin count) :
    MovingPatchSourceComparison where
  first := comparison.first.patch index
  second := comparison.second.patch index
  density := comparison.first.density index
  firstReceiver := comparison.firstReceiver comparison.time
  secondReceiver := comparison.secondReceiver comparison.time
  receiverRadius := comparison.receiverRadius
  receiverRadius_nonnegative := comparison.receiverRadius_nonnegative
  time := comparison.time
  initial := comparison.initial index
  final := comparison.final index
  firstShape := comparison.firstShape index
  secondShape := comparison.secondShape index
  radiusEqual := comparison.radiusEqual index
  phaseEqual := comparison.phaseEqual index
  firstArea := comparison.firstArea index
  secondArea := comparison.secondArea index

theorem exteriorTaylorCoefficient_difference_eq_sum {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison count) (selected : Finset (Fin count)) (power : ℕ) :
    comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time =
      ∑ index ∈ selected, (comparison.source index).coefficientDifference power := by
  rw [comparison.first.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient,
    comparison.second.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  dsimp only [MovingPatchSourceComparison.coefficientDifference, source]
  rw [comparison.densityEqual index]

theorem exteriorTaylorCoefficient_weighted_difference_le_sum {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison count) (selected : Finset (Fin count))
    {weight : ℝ} (nonnegative : 0 ≤ weight) (power : ℕ) :
    weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖ ≤
      ∑ index ∈ selected, weight ^ (power + 1) * ‖(comparison.source index).coefficientDifference power‖ := by
  rw [comparison.exteriorTaylorCoefficient_difference_eq_sum selected power, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg nonnegative (power + 1))

end MovingPatchFamilySourceComparison

end EulerNonuniqueness.Paper
