import EulerNonuniqueness.Section3.IndependentForcingDenominators
import EulerNonuniqueness.General.FiniteResonantSelection

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance independentResonantRemainderC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentForcingResonantCoefficient_eq_zero (degree : ℕ) (positive : 0 < degree) :
    independentForcingResonantCoefficient degree = 0 := by
  unfold independentForcingResonantCoefficient EulerNonuniqueness.General.finiteSpectralResonantPart
  apply Finset.sum_eq_zero
  intro output _
  apply Finset.sum_eq_zero
  intro input _
  rw [if_neg]
  intro resonance
  have zero := (independentForcingDenominator_zero_iff degree output input).mp resonance
  omega

theorem independentForcingResonantCoefficient_zero_degree :
    independentForcingResonantCoefficient 0 =
      independentDiskNegativeProjection.comp
        ((independentForcingLinearCoefficient 0).comp independentDiskPositiveProjection) := by
  unfold independentForcingResonantCoefficient
  have unique (output input : Fin 3) :
      -Complex.I * ((0 + 2 : ℕ) : ℂ) / 2 + independentDiskSpectralEigenvalue input -
        independentDiskSpectralEigenvalue output = 0 ↔ output = 2 ∧ input = 1 := by
    exact (independentForcingDenominator_zero_iff 0 output input).trans
      ⟨fun hypothesis => hypothesis.2, fun hypothesis => ⟨rfl, hypothesis⟩⟩
  have result := EulerNonuniqueness.General.finiteSpectralResonantPart_of_unique
    independentDiskSpectralProjection independentDiskSpectralEigenvalue
    (-Complex.I * ((0 + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCoefficient 0) 2 1 unique
  have negative : independentDiskSpectralProjection 2 = independentDiskNegativeProjection := rfl
  have positive : independentDiskSpectralProjection 1 = independentDiskPositiveProjection := rfl
  rw [negative, positive] at result
  exact result

theorem independentForcingLinearCorrection_equation_of_degree_pos (degree : ℕ) (positive : 0 < degree) :
    EulerNonuniqueness.General.linearHomologicalOperator independentDiskRotatingDerivative
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCorrection degree) =
      independentForcingLinearCoefficient degree := by
  rw [independentForcingLinearCorrection_equation,
    independentForcingResonantCoefficient_eq_zero degree positive, sub_zero]

end

end EulerNonuniqueness.Paper
