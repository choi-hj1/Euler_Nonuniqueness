import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseBounds
import EulerNonuniqueness.Section3.DiskSpectralScaledSlope
import EulerNonuniqueness.Section3.ContourNormalizationRegularity
import EulerNonuniqueness.General.QuadraticObservableLipschitz

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance normalizedQuadraticC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def diskSpectralQuadraticObservable (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.quadraticCoordinate
    (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM data)) 1 (diskPhysicalTransverseProjection data)

def diskNormalizedQuadraticObservable (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskSpectralQuadraticObservable (diskPhysicalSpectralCoordinate (contourAreaCentroidNormalization data))

theorem diskSpectralQuadraticObservable_zero : diskSpectralQuadraticObservable 0 = 0 := by
  simp only [diskSpectralQuadraticObservable, map_zero, EulerNonuniqueness.General.quadraticCoordinate,
    div_one, one_smul, sub_zero]

theorem diskNormalizedQuadraticObservable_circle :
    diskNormalizedQuadraticObservable standardCircleBanach = 0 := by
  rw [diskNormalizedQuadraticObservable, contourAreaCentroidNormalization_circle,
    diskPhysicalSpectralCoordinate_circle, diskSpectralQuadraticObservable_zero]

theorem diskSpectralQuadraticObservable_lipschitzNear_zero :
    EulerNonuniqueness.General.LipschitzNear diskSpectralQuadraticObservable (0 : PeriodicC1HolderHalf) := by
  have neutralRegular : EulerNonuniqueness.General.LipschitzNear
      (diskRelabelNeutralCLM : PeriodicC1HolderHalf → PeriodicC1HolderHalf) 0 :=
    EulerNonuniqueness.General.lipschitzNear_of_contDiffAt_one diskRelabelNeutralCLM.contDiff.contDiffAt
  have transverseRegular : EulerNonuniqueness.General.LipschitzNear
      (diskPhysicalTransverseProjection : PeriodicC1HolderHalf → PeriodicC1HolderHalf) 0 :=
    EulerNonuniqueness.General.lipschitzNear_of_contDiffAt_one diskPhysicalTransverseProjection.contDiff.contDiffAt
  have coefficientRegular : EulerNonuniqueness.General.LipschitzNear
      (fun data : PeriodicC1HolderHalf => diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM data)) 0 := by
    apply EulerNonuniqueness.General.LipschitzNear.comp
      (outer := diskSpectralMovingQuadraticCorrection) (inner := diskRelabelNeutralCLM)
    · simpa only [map_zero] using diskSpectralMovingQuadraticCorrection_lipschitzNear
    · exact neutralRegular
  exact EulerNonuniqueness.General.lipschitzNear_quadraticCoordinate coefficientRegular transverseRegular

theorem diskNormalizedQuadraticObservable_lipschitzNear_circle :
    EulerNonuniqueness.General.LipschitzNear diskNormalizedQuadraticObservable standardCircleBanach := by
  have normalizationRegular : EulerNonuniqueness.General.LipschitzNear
      contourAreaCentroidNormalization standardCircleBanach :=
    EulerNonuniqueness.General.lipschitzNear_of_contDiffAt_one
      ((contourAreaCentroidNormalization_contDiffAt_two standardCircleBanach (by simp)).of_le (by norm_num))
  have inverseRegular : EulerNonuniqueness.General.LipschitzNear
      (fun data => diskPhysicalSpectralCoordinate (contourAreaCentroidNormalization data)) standardCircleBanach := by
    apply EulerNonuniqueness.General.LipschitzNear.comp
      (outer := diskPhysicalSpectralCoordinate) (inner := contourAreaCentroidNormalization)
    · simpa only [contourAreaCentroidNormalization_circle] using diskPhysicalSpectralCoordinate_lipschitzNear_circle
    · exact normalizationRegular
  apply EulerNonuniqueness.General.LipschitzNear.comp
    (outer := diskSpectralQuadraticObservable)
    (inner := fun data => diskPhysicalSpectralCoordinate (contourAreaCentroidNormalization data))
  · simpa only [contourAreaCentroidNormalization_circle, diskPhysicalSpectralCoordinate_circle] using
      diskSpectralQuadraticObservable_lipschitzNear_zero
  · exact inverseRegular

end EulerNonuniqueness.Paper
