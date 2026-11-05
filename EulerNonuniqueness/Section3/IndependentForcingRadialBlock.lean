import EulerNonuniqueness.Section3.IndependentForcingLinearCoefficient
import EulerNonuniqueness.Section3.ContourAngularSelection
import EulerNonuniqueness.General.WeightedBlockCovariance

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentRadialBlockC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def c1MultiplierCCLM (multiplier : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexLinearFromReal (c1ProductCLM multiplier) (by
    intro direction
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change multiplier.val.1 label * (Complex.I * direction.val.1 label) =
      Complex.I * (multiplier.val.1 label * direction.val.1 label)
    ring)

theorem c1MultiplierCCLM_value (multiplier data : PeriodicC1HolderHalf) (label : ℝ) :
    (c1MultiplierCCLM multiplier data).val.1 label = multiplier.val.1 label * data.val.1 label := rfl

def independentPositiveMaterial : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  (0 : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf).prod
    ((2 : ℂ) • c1MultiplierCCLM (c1Conjugate standardCircleBanach))

def independentNegativeRadial : (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf :=
  (1 / 2 : ℂ) • (c1MultiplierCCLM (c1Conjugate standardCircleBanach)).comp
    (ContinuousLinearMap.fst ℂ PeriodicC1HolderHalf PeriodicC1HolderHalf)

theorem independentPositiveMaterial_shift (offset : ℝ) (data : PeriodicC1HolderHalf) :
    contourIndependentShift offset (independentPositiveMaterial data) =
      independentPositiveMaterial (contourLabelShiftCCLM offset data) := by
  rw [contourIndependentShift_eq_diagonal]
  apply Prod.ext
  · simp only [independentPositiveMaterial, ContinuousLinearMap.coe_prodMap', Prod.map,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply, map_zero]
  · apply PeriodicC1HolderHalf.ext_value
    intro label
    change (standardCircle offset) ^ 2 * ((standardCircle offset)⁻¹ *
        ((2 : ℂ) * (star (standardCircle (label + offset)) * data.val.1 (label + offset)))) =
      (2 : ℂ) * (star (standardCircle label) * (contourLabelShiftCCLM offset data).val.1 label)
    rw [contourLabelShiftCCLM_value, standardCircle_add, star_mul, standardCircle_star_eq_inv]
    have nonzero : standardCircle offset ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
    field_simp
    <;> ring

theorem independentNegativeRadial_shift (offset : ℝ) (data : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourLabelShiftCCLM offset (independentNegativeRadial data) =
      independentNegativeRadial (contourIndependentShift offset data) := by
  rw [contourIndependentShift_eq_diagonal]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value]
  change (1 / 2 : ℂ) * (star (standardCircle (label + offset)) * data.1.val.1 (label + offset)) =
    (1 / 2 : ℂ) * (star (standardCircle label) *
      ((standardCircle offset)⁻¹ * data.1.val.1 (label + offset)))
  rw [standardCircle_add, star_mul, standardCircle_star_eq_inv]
  ring

def independentForcingRadialBlock (degree : ℕ) : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.weightedOperatorBlock independentNegativeRadial
    (independentForcingLinearCoefficient degree) independentPositiveMaterial

theorem independentForcingRadialBlock_angular (degree : ℕ) (offset : ℝ) (data : PeriodicC1HolderHalf) :
    contourLabelShiftCCLM offset (independentForcingRadialBlock degree data) =
      ((standardCircle offset)⁻¹ ^ (degree + 2)) •
        independentForcingRadialBlock degree (contourLabelShiftCCLM offset data) := by
  unfold independentForcingRadialBlock
  with_reducible
    exact EulerNonuniqueness.General.weightedOperatorBlock_covariance independentNegativeRadial
      (independentForcingLinearCoefficient degree) independentPositiveMaterial
      (contourLabelShiftCCLM offset) (contourIndependentShift offset)
      ((standardCircle offset)⁻¹ ^ (degree + 2)) (independentNegativeRadial_shift offset)
      (independentPositiveMaterial_shift offset) (independentForcingLinearCoefficient_angular degree offset) data

end

end EulerNonuniqueness.Paper
