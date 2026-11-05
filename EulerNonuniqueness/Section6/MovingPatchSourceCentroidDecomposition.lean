import EulerNonuniqueness.Section6.MovingPatchSourceCorrectionSeries
import EulerNonuniqueness.Section6.MovingPatchCenteredSourceSeries

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

namespace MovingMaterialPatch

def sourceTaylorCentroidCoefficient (path : MovingMaterialPatch) (density : ℝ) (receiver : ℂ)
    (receiverRadius : ℝ) (power : ℕ) (time : ℝ) : ℂ :=
  ((-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
    ((density * volume.real (path.domain time)) • (star (receiver - path.center time))⁻¹ ^ (power + 2))

theorem sourceTaylorCoefficient_eq_centroidCoefficient_add_correction (path : MovingMaterialPatch)
    (density : ℝ) (receiver : ℂ) (receiverRadius : ℝ) (power : ℕ) (time : ℝ) :
    path.sourceTaylorCoefficient density receiver receiverRadius power time =
      path.sourceTaylorCentroidCoefficient density receiver receiverRadius power time +
      path.sourceTaylorCentroidCorrection density receiver receiverRadius power time :=
  path.sourceTaylorCoefficient_eq_centroid_and_correction density receiver receiverRadius power time

theorem sourceTaylorCentroidCoefficient_eq_of_same_displacement (first second : MovingMaterialPatch)
    (density : ℝ) (firstReceiver secondReceiver : ℂ) (receiverRadius : ℝ) (power : ℕ) (time : ℝ)
    (areaEqual : volume.real (first.domain time) = volume.real (second.domain time))
    (displacementEqual : firstReceiver - first.center time = secondReceiver - second.center time) :
    first.sourceTaylorCentroidCoefficient density firstReceiver receiverRadius power time =
      second.sourceTaylorCentroidCoefficient density secondReceiver receiverRadius power time := by
  simp only [sourceTaylorCentroidCoefficient, areaEqual, displacementEqual]

theorem sourceTaylorCentroidCorrection_difference_eq_of_same_displacement (first second : MovingMaterialPatch)
    (density : ℝ) (firstReceiver secondReceiver : ℂ) (receiverRadius : ℝ) (power : ℕ) (time : ℝ)
    (areaEqual : volume.real (first.domain time) = volume.real (second.domain time))
    (displacementEqual : firstReceiver - first.center time = secondReceiver - second.center time) :
    first.sourceTaylorCentroidCorrection density firstReceiver receiverRadius power time -
      second.sourceTaylorCentroidCorrection density secondReceiver receiverRadius power time =
    first.sourceTaylorCoefficient density firstReceiver receiverRadius power time -
      second.sourceTaylorCoefficient density secondReceiver receiverRadius power time := by
  rw [first.sourceTaylorCoefficient_eq_centroidCoefficient_add_correction,
    second.sourceTaylorCoefficient_eq_centroidCoefficient_add_correction,
    first.sourceTaylorCentroidCoefficient_eq_of_same_displacement second density firstReceiver secondReceiver
      receiverRadius power time areaEqual displacementEqual]
  abel

end MovingMaterialPatch

namespace MovingPatchSourceComparison

def centroidCoefficientDifference (comparison : MovingPatchSourceComparison) (power : ℕ) : ℂ :=
  comparison.first.sourceTaylorCentroidCoefficient comparison.density comparison.firstReceiver
      comparison.receiverRadius power comparison.time -
    comparison.second.sourceTaylorCentroidCoefficient comparison.density comparison.secondReceiver
      comparison.receiverRadius power comparison.time

def centroidCorrectionDifference (comparison : MovingPatchSourceComparison) (power : ℕ) : ℂ :=
  comparison.first.sourceTaylorCentroidCorrection comparison.density comparison.firstReceiver
      comparison.receiverRadius power comparison.time -
    comparison.second.sourceTaylorCentroidCorrection comparison.density comparison.secondReceiver
      comparison.receiverRadius power comparison.time

theorem coefficientDifference_eq_centroid_add_correction (comparison : MovingPatchSourceComparison) (power : ℕ) :
    comparison.coefficientDifference power =
      comparison.centroidCoefficientDifference power + comparison.centroidCorrectionDifference power := by
  unfold coefficientDifference centroidCoefficientDifference centroidCorrectionDifference
  rw [comparison.first.sourceTaylorCoefficient_eq_centroidCoefficient_add_correction,
    comparison.second.sourceTaylorCoefficient_eq_centroidCoefficient_add_correction]
  abel

theorem hybrid_centroidCorrectionDifference_eq_shapeDifference (comparison : MovingPatchSourceComparison) (power : ℕ) :
    comparison.first.sourceTaylorCentroidCorrection comparison.density comparison.hybridReceiver
        comparison.receiverRadius power comparison.time -
      comparison.second.sourceTaylorCentroidCorrection comparison.density comparison.secondReceiver
        comparison.receiverRadius power comparison.time =
    comparison.first.sourceTaylorCoefficient comparison.density comparison.hybridReceiver
        comparison.receiverRadius power comparison.time -
      comparison.second.sourceTaylorCoefficient comparison.density comparison.secondReceiver
        comparison.receiverRadius power comparison.time := by
  apply MovingMaterialPatch.sourceTaylorCentroidCorrection_difference_eq_of_same_displacement
  · rw [comparison.firstArea, comparison.secondArea, comparison.radiusEqual]
  · exact comparison.hybridReceiver_displacement

end MovingPatchSourceComparison

end EulerNonuniqueness.Paper
