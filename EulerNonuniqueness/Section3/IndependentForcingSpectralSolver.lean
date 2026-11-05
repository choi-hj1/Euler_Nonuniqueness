import EulerNonuniqueness.Section3.IndependentDiskSpectrum
import EulerNonuniqueness.General.FiniteSpectralHomological
import EulerNonuniqueness.General.ComplexCubicResolution

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentForcingSolverC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentDiskSpectralProjection (branch : Fin 3) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexCubicProjection independentDiskRotatingDerivative branch

def independentDiskSpectralEigenvalue (branch : Fin 3) : ℂ :=
  EulerNonuniqueness.General.complexCubicEigenvalue branch

theorem independentDiskSpectralProjection_complete :
    ∑ branch, independentDiskSpectralProjection branch =
      ContinuousLinearMap.id ℂ (PeriodicC1HolderHalf × PeriodicC1HolderHalf) := by
  unfold independentDiskSpectralProjection
  with_reducible exact EulerNonuniqueness.General.complexCubicProjection_complete independentDiskRotatingDerivative

theorem independentDiskSpectralProjection_left (branch : Fin 3) :
    independentDiskRotatingDerivative.comp (independentDiskSpectralProjection branch) =
      independentDiskSpectralEigenvalue branch • independentDiskSpectralProjection branch := by
  unfold independentDiskSpectralProjection independentDiskSpectralEigenvalue
  with_reducible
    exact EulerNonuniqueness.General.complexCubicProjection_left independentDiskRotatingDerivative
      independentDiskRotatingDerivative_cubic branch

theorem independentDiskSpectralProjection_right (branch : Fin 3) :
    (independentDiskSpectralProjection branch).comp independentDiskRotatingDerivative =
      independentDiskSpectralEigenvalue branch • independentDiskSpectralProjection branch := by
  unfold independentDiskSpectralProjection independentDiskSpectralEigenvalue
  with_reducible
    exact EulerNonuniqueness.General.complexCubicProjection_right independentDiskRotatingDerivative
      independentDiskRotatingDerivative_cubic branch

def independentForcingLinearCorrection (degree : ℕ) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.finiteSpectralHomologicalSolver independentDiskSpectralProjection
    independentDiskSpectralEigenvalue (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2)
    (independentForcingLinearCoefficient degree)

def independentForcingResonantCoefficient (degree : ℕ) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.finiteSpectralResonantPart independentDiskSpectralProjection
    independentDiskSpectralEigenvalue (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2)
    (independentForcingLinearCoefficient degree)

theorem independentForcingLinearCorrection_equation (degree : ℕ) :
    EulerNonuniqueness.General.linearHomologicalOperator independentDiskRotatingDerivative
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCorrection degree) =
      independentForcingLinearCoefficient degree - independentForcingResonantCoefficient degree := by
  unfold independentForcingLinearCorrection independentForcingResonantCoefficient
  with_reducible
    exact EulerNonuniqueness.General.finiteSpectralHomologicalSolver_equation
      independentDiskRotatingDerivative independentDiskSpectralProjection independentDiskSpectralEigenvalue
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCoefficient degree)
      independentDiskSpectralProjection_complete independentDiskSpectralProjection_left
      independentDiskSpectralProjection_right

theorem independentForcingLinearCorrection_norm_le (degree : ℕ) :
    ‖independentForcingLinearCorrection degree‖ ≤
      ∑ output : Fin 3, ∑ input : Fin 3,
        ‖(-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2 + independentDiskSpectralEigenvalue input -
          independentDiskSpectralEigenvalue output)⁻¹‖ * ‖independentDiskSpectralProjection output‖ *
          ‖independentForcingLinearCoefficient degree‖ * ‖independentDiskSpectralProjection input‖ := by
  unfold independentForcingLinearCorrection
  with_reducible
    exact EulerNonuniqueness.General.finiteSpectralHomologicalSolver_norm_le
      independentDiskSpectralProjection independentDiskSpectralEigenvalue
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCoefficient degree)

end

end EulerNonuniqueness.Paper
