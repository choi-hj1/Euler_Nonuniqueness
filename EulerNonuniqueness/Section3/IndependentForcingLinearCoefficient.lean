import EulerNonuniqueness.Section3.IndependentCenteredForcingDerivative
import EulerNonuniqueness.General.WeightedQuadraticLinearCoefficient

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentLinearForcingC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentForcingPrimitiveValue (degree : ℕ) : PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  (diskForcingPrimitiveFactor degree 1 • c1Conjugate (diskCircleMode (degree + 1)), 0)

theorem independentForcingPrimitiveValue_angular (degree : ℕ) (offset : ℝ) :
    contourIndependentShift offset (independentForcingPrimitiveValue degree) =
      ((standardCircle offset)⁻¹ ^ (degree + 2)) • independentForcingPrimitiveValue degree := by
  rw [contourIndependentShift_eq_diagonal]
  apply Prod.ext
  · apply PeriodicC1HolderHalf.ext_value
    intro label
    change (standardCircle offset)⁻¹ *
        (diskForcingPrimitiveFactor degree 1 * star ((diskCircleMode (degree + 1)).val.1 (label + offset))) =
      (standardCircle offset)⁻¹ ^ (degree + 2) *
        (diskForcingPrimitiveFactor degree 1 * star ((diskCircleMode (degree + 1)).val.1 label))
    rw [diskCircleMode_value, diskCircleMode_value, standardCircle_add, mul_pow, star_mul, star_pow, star_pow,
      standardCircle_star_eq_inv]
    rw [show degree + 2 = (degree + 1) + 1 by omega, pow_succ]
    ring
  · simp only [independentForcingPrimitiveValue, ContinuousLinearMap.coe_prodMap', Prod.map, Prod.smul_snd, map_zero, smul_zero]

def independentForcingLinearCoefficient (degree : ℕ) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.forcingLinearCoefficient (independentCenteredForcingDerivative degree)
    contourIndependentQuadratic (independentForcingPrimitiveValue degree)

theorem independentForcingLinearCoefficient_angular (degree : ℕ) (offset : ℝ)
    (direction : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourIndependentShift offset (independentForcingLinearCoefficient degree direction) =
      ((standardCircle offset)⁻¹ ^ (degree + 2)) •
        independentForcingLinearCoefficient degree (contourIndependentShift offset direction) := by
  unfold independentForcingLinearCoefficient
  with_reducible
    exact EulerNonuniqueness.General.forcingLinearCoefficient_weighted
      (independentCenteredForcingDerivative degree) contourIndependentQuadratic (independentForcingPrimitiveValue degree)
      (contourIndependentShift offset) ((standardCircle offset)⁻¹ ^ (degree + 2))
      (independentCenteredForcingDerivative_angular degree offset)
      (contourIndependentQuadratic_normalized_shift offset)
      (independentForcingPrimitiveValue_angular degree offset) direction

end

end EulerNonuniqueness.Paper
