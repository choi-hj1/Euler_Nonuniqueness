import EulerNonuniqueness.Section3.RelabeledPrimitiveAngularDerivative
import EulerNonuniqueness.General.OperatorPairComposition

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

theorem tsum_relabeledPrimitiveCoefficient_weight96_le {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    (∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖diskForcingPrimitiveFactor degree frequency * amplitude degree time‖) ≤
    (2 / |frequency|) * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) := by
  have coefficients := summable_relabeledPrimitiveCoefficient_weight96 nonzero amplitude time weighted
  have term (degree : ℕ) : (96 : ℝ) ^ (degree + 1) *
      ‖diskForcingPrimitiveFactor degree frequency * amplitude degree time‖ ≤
      (2 / |frequency|) * ((96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) := by
    rw [norm_mul]
    have actual := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (diskForcingPrimitiveFactor_norm_le nonzero degree) (norm_nonneg (amplitude degree time)))
      (by positivity : 0 ≤ (96 : ℝ) ^ (degree + 1))
    exact actual.trans_eq (by ring)
  simpa only [tsum_mul_left] using Summable.tsum_le_tsum term coefficients (weighted.mul_left (2 / |frequency|))

theorem relabeledPrimitiveAngularDerivative_norm_le_weight96
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (angular : PeriodicC1HolderHalf) (bounded : ‖diskRelabelCurve angular 1‖ ≤ 3)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    ‖relabeledPrimitiveAngularDerivative frequency amplitude time angular‖ ≤
    (2 / |frequency|) * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) *
      ‖fderiv ℝ (fun current => diskRelabelCurve current 1) angular‖ := by
  have coefficientWeighted := summable_relabeledPrimitiveCoefficient_weight96 nonzero amplitude time weighted
  have raw := exteriorContourPowerSeriesFirstJet_norm_bound96 (Circle.exp (frequency * time / 2))
    (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
    (diskRelabelCurve angular 1) bounded coefficientWeighted
  have scalar := tsum_relabeledPrimitiveCoefficient_weight96_le nonzero amplitude time weighted
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (raw.trans scalar) (norm_nonneg _))

theorem relabeledPrimitiveAngularDerivative_pair_difference_le_weight96
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (first final : PeriodicC1HolderHalf)
    (firstBound : ‖diskRelabelCurve first 1‖ ≤ 5 / 2) (finalBound : ‖diskRelabelCurve final 1‖ ≤ 5 / 2)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    ‖relabeledPrimitiveAngularDerivative frequency amplitude time first -
      relabeledPrimitiveAngularDerivative frequency amplitude time final‖ ≤
    (2 / |frequency|) * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) *
      (‖fderiv ℝ (fun current => diskRelabelCurve current 1) first -
          fderiv ℝ (fun current => diskRelabelCurve current 1) final‖ +
        8 * ‖diskRelabelCurve first 1 - diskRelabelCurve final 1‖ *
          ‖fderiv ℝ (fun current => diskRelabelCurve current 1) final‖) := by
  let coefficient := fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time
  let phase := Circle.exp (frequency * time / 2)
  have coefficientWeighted := summable_relabeledPrimitiveCoefficient_weight96 nonzero amplitude time weighted
  have rawAbsolute := exteriorContourPowerSeriesFirstJet_norm_bound96 phase coefficient
    (diskRelabelCurve first 1) (by linarith) coefficientWeighted
  have rawDifference := exteriorContourPowerSeriesFirstJet_difference_norm_le phase coefficient
    (diskRelabelCurve first 1) (diskRelabelCurve final 1) firstBound finalBound coefficientWeighted
  have composition := EulerNonuniqueness.General.norm_operator_comp_difference_le
    (exteriorContourPowerSeriesFirstJet phase coefficient (diskRelabelCurve first 1))
    (exteriorContourPowerSeriesFirstJet phase coefficient (diskRelabelCurve final 1))
    (fderiv ℝ (fun current => diskRelabelCurve current 1) first)
    (fderiv ℝ (fun current => diskRelabelCurve current 1) final)
  have estimate := composition.trans (add_le_add
    (mul_le_mul_of_nonneg_right rawAbsolute (norm_nonneg _))
    (mul_le_mul_of_nonneg_right rawDifference (norm_nonneg _)))
  have scalar := mul_le_mul_of_nonneg_right (tsum_relabeledPrimitiveCoefficient_weight96_le nonzero amplitude time weighted)
    (by positivity : 0 ≤
      ‖fderiv ℝ (fun current => diskRelabelCurve current 1) first - fderiv ℝ (fun current => diskRelabelCurve current 1) final‖ +
        8 * ‖diskRelabelCurve first 1 - diskRelabelCurve final 1‖ * ‖fderiv ℝ (fun current => diskRelabelCurve current 1) final‖)
  apply estimate.trans
  convert scalar using 1 <;> ring

end EulerNonuniqueness.Paper
