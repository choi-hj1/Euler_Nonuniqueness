import EulerNonuniqueness.Section3.IndependentForcingValueEquation
import EulerNonuniqueness.Section3.DiskPhysicalCubicSpectrum
import EulerNonuniqueness.General.ComplexPairCubic
import EulerNonuniqueness.General.ComplexCubicSpectral

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentDiskSpectrumC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentDiskRotatingDerivative_cubic (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivative (independentDiskRotatingDerivative
      (independentDiskRotatingDerivative pair)) = (-1 / 4 : ℂ) • independentDiskRotatingDerivative pair := by
  unfold independentDiskRotatingDerivative
  with_reducible
    exact EulerNonuniqueness.General.complexPairExtension_cubic c1ConjugateCLM
      c1ConjugateCLM_complex_smul c1ConjugateCLM_involution diskRotatingDerivative
      diskRotatingDerivative_cubic pair

def independentDiskNeutralProjection :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexCubicNeutral independentDiskRotatingDerivative

def independentDiskPositiveProjection :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexCubicPositive independentDiskRotatingDerivative

def independentDiskNegativeProjection :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexCubicNegative independentDiskRotatingDerivative

theorem independentDiskSpectral_decomposition :
    independentDiskNeutralProjection + independentDiskPositiveProjection + independentDiskNegativeProjection =
      ContinuousLinearMap.id ℂ (PeriodicC1HolderHalf × PeriodicC1HolderHalf) := by
  simpa only [independentDiskNeutralProjection, independentDiskPositiveProjection, independentDiskNegativeProjection]
    using (EulerNonuniqueness.General.complexCubic_decomposition independentDiskRotatingDerivative)

theorem independentDiskNeutralProjection_eigen (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivative (independentDiskNeutralProjection pair) = 0 := by
  unfold independentDiskNeutralProjection
  with_reducible
    exact EulerNonuniqueness.General.complexCubicNeutral_eigen independentDiskRotatingDerivative
      independentDiskRotatingDerivative_cubic pair

theorem independentDiskPositiveProjection_eigen (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivative (independentDiskPositiveProjection pair) =
      (Complex.I / 2) • independentDiskPositiveProjection pair := by
  unfold independentDiskPositiveProjection
  with_reducible
    exact EulerNonuniqueness.General.complexCubicPositive_eigen independentDiskRotatingDerivative
      independentDiskRotatingDerivative_cubic pair

theorem independentDiskNegativeProjection_eigen (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivative (independentDiskNegativeProjection pair) =
      (-Complex.I / 2) • independentDiskNegativeProjection pair := by
  unfold independentDiskNegativeProjection
  with_reducible
    exact EulerNonuniqueness.General.complexCubicNegative_eigen independentDiskRotatingDerivative
      independentDiskRotatingDerivative_cubic pair

end

end EulerNonuniqueness.Paper
