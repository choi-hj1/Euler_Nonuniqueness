import EulerNonuniqueness.General.ComplexCubicProjectionRegularity
import EulerNonuniqueness.Section3.MovingStrainGeneratorRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] movingStrainGeneratorC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentDiskSpectralProjectionAt_lipschitzNear (branch : Fin 3) :
    EulerNonuniqueness.General.LipschitzNear
      (fun data => independentDiskSpectralProjectionAt data branch) standardCircleBanach := by
  have smooth := EulerNonuniqueness.General.complexCubicProjection_contDiff
    (Space := PeriodicC1HolderHalf × PeriodicC1HolderHalf) branch
  have realSmooth := smooth.restrict_scalars ℝ
  have outer := EulerNonuniqueness.General.lipschitzNear_of_contDiffAt_one
    (realSmooth.contDiffAt (x := independentDiskRotatingDerivativeAt standardCircleBanach))
  exact outer.comp independentDiskRotatingDerivativeAt_lipschitzNear

end EulerNonuniqueness.Paper
