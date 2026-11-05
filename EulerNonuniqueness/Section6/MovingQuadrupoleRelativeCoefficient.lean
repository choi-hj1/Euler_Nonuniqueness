import EulerNonuniqueness.Section6.MovingQuadrupoleSourceDecomposition
import EulerNonuniqueness.Section6.MovingPatchFamilySourceComparison
import EulerNonuniqueness.Section6.MovingPatchSourceCorrectionRelative
import EulerNonuniqueness.Section6.PointSourceFullRelativeSeries

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

theorem quadrupoleCoefficient_difference_eq_point_and_corrections
    (comparison : MovingPatchFamilySourceComparison 4) (circulation : ℝ)
    (firstCenter secondCenter : ℂ) (power : ℕ)
    (masses : ∀ patch, comparison.first.density patch *
      volume.real ((comparison.first.patch patch).domain comparison.time) =
        circulation * Section6.fourPointSign patch) :
    comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
      comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time =
    (Section6.pointSourceTaylorCoefficient circulation comparison.receiverRadius
        (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter)
        (comparison.firstReceiver comparison.time - firstCenter) power -
      Section6.pointSourceTaylorCoefficient circulation comparison.receiverRadius
        (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)
        (comparison.secondReceiver comparison.time - secondCenter) power) +
      ∑ patch : Fin 4, (comparison.source patch).centroidCorrectionDifference power := by
  have secondMasses (patch : Fin 4) : comparison.second.density patch *
      volume.real ((comparison.second.patch patch).domain comparison.time) =
        circulation * Section6.fourPointSign patch := by
    rw [← comparison.densityEqual patch, comparison.secondArea patch, ← comparison.radiusEqual patch,
      ← comparison.firstArea patch]
    exact masses patch
  rw [comparison.first.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient,
    comparison.second.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient]
  rw [quadrupole_sourceTaylorCoefficient_difference_eq_pointSource_and_corrections
    comparison.first.patch comparison.second.patch comparison.first.density comparison.second.density
    circulation comparison.receiverRadius (comparison.firstReceiver comparison.time) (comparison.secondReceiver comparison.time)
    firstCenter secondCenter power comparison.time masses secondMasses]
  congr 1
  apply Finset.sum_congr rfl
  intro patch _
  dsimp only [MovingPatchSourceComparison.centroidCorrectionDifference, source]
  rw [comparison.densityEqual patch]

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
