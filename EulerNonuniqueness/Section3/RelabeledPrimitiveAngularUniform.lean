import EulerNonuniqueness.Section3.RelabeledPrimitiveAngularRelative
import EulerNonuniqueness.Section3.RelabelMapUniformLipschitz
import EulerNonuniqueness.General.LocalC1LipschitzBounds

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

theorem relabeledPrimitiveAngularDerivative_exists_uniform_weight96_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {frequency : ℝ}, frequency ≠ 0 → ∀ (amplitude : ℕ → ℝ → ℂ) (time : ℝ),
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) →
      (∀ angular : PeriodicC1HolderHalf, ‖angular‖ ≤ radius →
        ‖relabeledPrimitiveAngularDerivative frequency amplitude time angular‖ ≤
          constant * ((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) / |frequency|)) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖final‖ ≤ radius →
        ‖relabeledPrimitiveAngularDerivative frequency amplitude time first -
          relabeledPrimitiveAngularDerivative frequency amplitude time final‖ ≤
          constant * ((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) / |frequency|) * ‖first - final‖ := by
  have regular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun angular => diskRelabelCurve angular 1) (0 : PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskRelabelMap_analyticAt 0)
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeOne, _, derivativeAbsolute, derivativeDifference⟩ :=
    regular.exists_uniform_derivative_ball
  obtain ⟨baseRadius, basePositive, baseConstant, _, baseDifference⟩ := diskRelabelMap_exists_uniform_lipschitz
  have near : ∀ᶠ angular in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskRelabelCurve angular 1‖ < 5 / 2 := by
    have baseZero : diskRelabelCurve (0 : PeriodicC1HolderHalf) 1 = standardCircleBanach := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rw [diskRelabelCurve_value]
      change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
      simp
    exact (diskRelabelMap_analyticAt 0).continuousAt.norm.eventually (gt_mem_nhds (by
      change ‖diskRelabelCurve (0 : PeriodicC1HolderHalf) 1‖ < 5 / 2
      rw [baseZero]
      linarith [standardCircleBanach_norm_bound]))
  obtain ⟨normRadius, normPositive, normSmall⟩ := Metric.eventually_nhds_iff.mp near
  let radius := min derivativeRadius (min baseRadius (normRadius / 2))
  let constant := 2 * derivativeConstant * (1 + 8 * (baseConstant : ℝ)) + 1
  have derivativeNonnegative : 0 ≤ derivativeConstant := by linarith
  have coefficientLe : 2 * derivativeConstant * (1 + 8 * (baseConstant : ℝ)) ≤ constant := by
    dsimp [constant]
    linarith
  have twoDerivativeLe : 2 * derivativeConstant ≤ constant := by
    dsimp [constant]
    nlinarith [mul_nonneg derivativeNonnegative baseConstant.coe_nonneg]
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ 2 * derivativeConstant * (1 + 8 * (baseConstant : ℝ)) := by positivity
    dsimp [constant]
    linarith
  have baseBound {angular : PeriodicC1HolderHalf} (inside : ‖angular‖ ≤ radius) : ‖diskRelabelCurve angular 1‖ ≤ 5 / 2 :=
    (normSmall (show dist angular 0 < normRadius by
      rw [dist_zero_right]
      exact (inside.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith))).le
  have derivativeBound {angular : PeriodicC1HolderHalf} (inside : ‖angular‖ ≤ radius) :
      ‖fderiv ℝ (fun current => diskRelabelCurve current 1) angular‖ ≤ derivativeConstant :=
    derivativeAbsolute angular (by simpa only [sub_zero] using inside.trans (min_le_left _ _))
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro frequency nonzero amplitude time weighted
  have sumNonnegative : 0 ≤ ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖ :=
    tsum_nonneg (fun degree => by positivity)
  constructor
  · intro angular inside
    have actual := (relabeledPrimitiveAngularDerivative_norm_le_weight96 nonzero amplitude time angular
      (by linarith [baseBound inside]) weighted).trans
      (mul_le_mul_of_nonneg_left (derivativeBound inside) (by positivity))
    have scalar := mul_le_mul_of_nonneg_right twoDerivativeLe
      (div_nonneg sumNonnegative (abs_nonneg frequency))
    exact actual.trans (by convert scalar using 1 <;> ring)
  · intro first final firstInside finalInside
    have firstJet := derivativeDifference first final
      (by simpa only [sub_zero] using firstInside.trans (min_le_left _ _))
      (by simpa only [sub_zero] using finalInside.trans (min_le_left _ _))
    have base := baseDifference first final
      (firstInside.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (finalInside.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have bracket := add_le_add firstJet (mul_le_mul_of_nonneg_left
      (mul_le_mul base (derivativeBound finalInside) (norm_nonneg _)
        (mul_nonneg baseConstant.coe_nonneg (norm_nonneg (first - final))))
      (by norm_num : (0 : ℝ) ≤ 8))
    have bracketBound :
        ‖fderiv ℝ (fun current => diskRelabelCurve current 1) first -
            fderiv ℝ (fun current => diskRelabelCurve current 1) final‖ +
          8 * ‖diskRelabelCurve first 1 - diskRelabelCurve final 1‖ *
            ‖fderiv ℝ (fun current => diskRelabelCurve current 1) final‖ ≤
        derivativeConstant * ‖first - final‖ + 8 * ((baseConstant : ℝ) * ‖first - final‖ * derivativeConstant) := by
      convert bracket using 1 <;> ring
    have actual := (relabeledPrimitiveAngularDerivative_pair_difference_le_weight96 nonzero amplitude time first final
      (baseBound firstInside) (baseBound finalInside) weighted).trans
      (mul_le_mul_of_nonneg_left bracketBound (by positivity))
    have scalar := mul_le_mul_of_nonneg_right coefficientLe
      (mul_nonneg (div_nonneg sumNonnegative (abs_nonneg frequency)) (norm_nonneg (first - final)))
    exact actual.trans (by convert scalar using 1 <;> ring)

end EulerNonuniqueness.Paper
