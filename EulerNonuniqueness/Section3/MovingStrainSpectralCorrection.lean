import EulerNonuniqueness.Section3.RelabeledForcingValueEquation
import EulerNonuniqueness.Section3.IndependentForcingDenominators
import EulerNonuniqueness.General.SpectralHomologicalLipschitz

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance movingStrainSpectralC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentStrainPrimitiveAt (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  (diskForcingPrimitiveFactor 0 1 • c1Conjugate data, 0)

def independentDiskSpectralProjectionAt (data : PeriodicC1HolderHalf) (branch : Fin 3) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexCubicProjection (independentDiskRotatingDerivativeAt data) branch

def independentStrainLinearCorrectionAt (data : PeriodicC1HolderHalf) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.finiteSpectralHomologicalSolver (independentDiskSpectralProjectionAt data)
    independentDiskSpectralEigenvalue (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2)
    (independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data))

theorem independentStrainLinearCorrectionAt_norm_le (data : PeriodicC1HolderHalf) :
    ‖independentStrainLinearCorrectionAt data‖ ≤
      2 * (∑ branch : Fin 3, ‖independentDiskSpectralProjectionAt data branch‖) ^ 2 *
        ‖independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data)‖ := by
  unfold independentStrainLinearCorrectionAt
  with_reducible
    exact EulerNonuniqueness.General.finiteSpectralHomologicalSolver_norm_le_uniform
      (independentDiskSpectralProjectionAt data) independentDiskSpectralEigenvalue
      (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2)
      (independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data))
      (independentForcingDenominator_inverse_norm_le 0)

end EulerNonuniqueness.Paper
