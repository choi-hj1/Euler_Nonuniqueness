import EulerNonuniqueness.General.ComplexCubicSolverRealRegularity
import EulerNonuniqueness.Section3.MovingStrainNumeratorRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] movingStrainGeneratorC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

local instance movingCorrectionRealOperatorSpace : NormedSpace ℝ
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf × PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)

theorem independentStrainLinearCorrectionAt_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear independentStrainLinearCorrectionAt standardCircleBanach := by
  have inner := independentDiskRotatingDerivativeAt_lipschitzNear.prodMk
    independentCentroidStrainNumeratorAt_lipschitzNear
  have outer := EulerNonuniqueness.General.complexCubicHomologicalSolver_lipschitzNear
    (Space := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    independentDiskSpectralEigenvalue (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2)
    (independentDiskRotatingDerivativeAt standardCircleBanach,
      independentCentroidStrainNumeratorAt standardCircleBanach (independentStrainPrimitiveAt standardCircleBanach))
  unfold independentStrainLinearCorrectionAt independentDiskSpectralProjectionAt
  with_reducible_and_instances
    exact EulerNonuniqueness.General.LipschitzNear.comp
      (inner := fun data => (independentDiskRotatingDerivativeAt data,
        independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data)))
      (point := standardCircleBanach) outer inner

end EulerNonuniqueness.Paper
