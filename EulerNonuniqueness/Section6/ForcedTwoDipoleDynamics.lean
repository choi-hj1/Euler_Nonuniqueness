import EulerNonuniqueness.Section6.ContinuedDipoleSeparation

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

def externalPairAverage (external : ℂ → ℂ) (center separation : ℂ) : ℂ :=
  (external (center + separation / 2) + external (center - separation / 2)) / 2

def externalPairDifference (external : ℂ → ℂ) (center separation : ℂ) : ℂ :=
  external (center + separation / 2) - external (center - separation / 2)

theorem twoDipole_first_pair_forced_equations
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {coefficient time : ℝ} {external : ℂ → ℂ} {residual : FourPointConfiguration}
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target +
        external (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + residual target) time) :
    HasDerivAt firstCenter
      (dipoleSelfVelocity coefficient (firstSeparation time) +
        dipoleCrossCenterVelocity coefficient (secondCenter time) (firstCenter time)
          (secondSeparation time) (firstSeparation time) +
        externalPairAverage external (firstCenter time) (firstSeparation time) + (residual 0 + residual 2) / 2) time ∧
      HasDerivAt firstSeparation
        (dipoleCrossRelativeVelocity coefficient (secondCenter time) (firstCenter time)
          (secondSeparation time) (firstSeparation time) +
          externalPairDifference external (firstCenter time) (firstSeparation time) + residual 0 - residual 2) time := by
  have positiveEquation := equation 0
  have negativeEquation := equation 2
  rw [fourPointField_twoDipoles] at positiveEquation negativeEquation
  simp only [twoDipoleConfiguration, Matrix.cons_val_zero, Matrix.cons_val_succ] at positiveEquation negativeEquation
  constructor
  · convert (positiveEquation.add negativeEquation).div_const 2 using 1
    · funext current
      dsimp
      ring
    · dsimp [dipoleSelfVelocity, dipoleCrossCenterVelocity, externalPairAverage]
      ring
  · convert positiveEquation.sub negativeEquation using 1
    · funext current
      dsimp
      ring
    · dsimp [dipoleCrossRelativeVelocity, externalPairDifference]
      ring

theorem externalPairDifference_bound {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0}
    (lipschitz : LipschitzOnWith strain external region) {center separation : ℂ}
    (positiveInside : center + separation / 2 ∈ region) (negativeInside : center - separation / 2 ∈ region) :
    ‖externalPairDifference external center separation‖ ≤ (strain : ℝ) * ‖separation‖ := by
  have control := (lipschitzOnWith_iff_norm_sub_le.mp lipschitz) positiveInside negativeInside
  have identity : center + separation / 2 - (center - separation / 2) = separation := by ring
  simpa only [externalPairDifference, identity] using control

theorem externalPairAverage_difference_bound {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0}
    (lipschitz : LipschitzOnWith strain external region)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (inside : ∀ target, twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈ region)
    (separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖firstCenter - secondCenter‖) :
    ‖externalPairAverage external firstCenter firstSeparation - externalPairAverage external secondCenter secondSeparation‖ ≤
      2 * (strain : ℝ) * ‖firstCenter - secondCenter‖ := by
  have positiveControl := (lipschitzOnWith_iff_norm_sub_le.mp lipschitz) (inside 0) (inside 1)
  have negativeControl := (lipschitzOnWith_iff_norm_sub_le.mp lipschitz) (inside 2) (inside 3)
  simp [twoDipoleConfiguration] at positiveControl negativeControl
  have positiveDistance : ‖firstCenter + firstSeparation / 2 - (secondCenter + secondSeparation / 2)‖ ≤
      2 * ‖firstCenter - secondCenter‖ := by
    have identity : firstCenter + firstSeparation / 2 - (secondCenter + secondSeparation / 2) =
        (firstCenter - secondCenter) + (firstSeparation / 2 - secondSeparation / 2) := by ring
    rw [identity]
    have triangle := norm_add_le (firstCenter - secondCenter) (firstSeparation / 2 - secondSeparation / 2)
    have offset := norm_sub_le (firstSeparation / 2) (secondSeparation / 2)
    simp only [norm_div, Complex.norm_ofNat] at offset
    linarith [norm_nonneg (firstCenter - secondCenter)]
  have negativeDistance : ‖firstCenter - firstSeparation / 2 - (secondCenter - secondSeparation / 2)‖ ≤
      2 * ‖firstCenter - secondCenter‖ := by
    have identity : firstCenter - firstSeparation / 2 - (secondCenter - secondSeparation / 2) =
        (firstCenter - secondCenter) - (firstSeparation / 2 - secondSeparation / 2) := by ring
    rw [identity]
    have triangle := norm_sub_le (firstCenter - secondCenter) (firstSeparation / 2 - secondSeparation / 2)
    have offset := norm_sub_le (firstSeparation / 2) (secondSeparation / 2)
    simp only [norm_div, Complex.norm_ofNat] at offset
    linarith [norm_nonneg (firstCenter - secondCenter)]
  have identity : externalPairAverage external firstCenter firstSeparation - externalPairAverage external secondCenter secondSeparation =
      ((external (firstCenter + firstSeparation / 2) - external (secondCenter + secondSeparation / 2)) +
        (external (firstCenter - firstSeparation / 2) - external (secondCenter - secondSeparation / 2))) / 2 := by
    dsimp [externalPairAverage]
    ring
  rw [identity, norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have triangle := norm_add_le (external (firstCenter + firstSeparation / 2) - external (secondCenter + secondSeparation / 2))
    (external (firstCenter - firstSeparation / 2) - external (secondCenter - secondSeparation / 2))
  nlinarith [mul_le_mul_of_nonneg_left positiveDistance strain.coe_nonneg,
    mul_le_mul_of_nonneg_left negativeDistance strain.coe_nonneg]

theorem residual_pair_difference_bound (residual : FourPointConfiguration) (first second : Fin 4) :
    ‖residual first - residual second‖ ≤ 2 * ‖residual‖ := by
  have firstBound := norm_le_pi_norm residual first
  have secondBound := norm_le_pi_norm residual second
  exact (norm_sub_le _ _).trans (by linarith)

theorem residual_pair_average_bound (residual : FourPointConfiguration) (first second : Fin 4) :
    ‖(residual first + residual second) / 2‖ ≤ ‖residual‖ := by
  rw [norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have firstBound := norm_le_pi_norm residual first
  have secondBound := norm_le_pi_norm residual second
  exact (norm_add_le _ _).trans (by linarith)

def twoDipoleExternalCenterCorrection (external : ℂ → ℂ) (residual : FourPointConfiguration)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ) : ℂ :=
  externalPairAverage external firstCenter firstSeparation - externalPairAverage external secondCenter secondSeparation +
    (residual 0 + residual 2) / 2 - (residual 1 + residual 3) / 2

theorem twoDipole_centers_actual_forced_equation
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {coefficient time : ℝ} {external : ℂ → ℂ} {residual : FourPointConfiguration}
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target +
        external (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + residual target) time) :
    HasDerivAt (fun current => firstCenter current - secondCenter current)
      (twoDipoleCenterRelativeVelocity coefficient (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) +
        twoDipoleExternalCenterCorrection external residual (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) time := by
  have firstDerivative := (twoDipole_first_pair_forced_equations equation).1
  have positiveEquation := equation 1
  have negativeEquation := equation 3
  rw [fourPointField_twoDipoles] at positiveEquation negativeEquation
  simp only [twoDipoleConfiguration, Matrix.cons_val_zero, Matrix.cons_val_succ] at positiveEquation negativeEquation
  have secondDerivative : HasDerivAt secondCenter
      (dipoleSelfVelocity coefficient (secondSeparation time) +
        dipoleCrossCenterVelocity coefficient (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) +
        externalPairAverage external (secondCenter time) (secondSeparation time) + (residual 1 + residual 3) / 2) time := by
    convert (positiveEquation.add negativeEquation).div_const 2 using 1
    · funext current
      dsimp
      ring
    · dsimp [dipoleSelfVelocity, dipoleCrossCenterVelocity, externalPairAverage]
      ring
  convert firstDerivative.sub secondDerivative using 1
  dsimp [twoDipoleCenterRelativeVelocity, twoDipoleExternalCenterCorrection]
  ring

theorem twoDipoleExternalCenterCorrection_bound {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0}
    (lipschitz : LipschitzOnWith strain external region) (residual : FourPointConfiguration)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (inside : ∀ target, twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈ region)
    (separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖firstCenter - secondCenter‖) :
    ‖twoDipoleExternalCenterCorrection external residual firstCenter secondCenter firstSeparation secondSeparation‖ ≤
      2 * (strain : ℝ) * ‖firstCenter - secondCenter‖ + 2 * ‖residual‖ := by
  have externalControl := externalPairAverage_difference_bound lipschitz inside separationBound
  have positiveControl := residual_pair_average_bound residual 0 2
  have negativeControl := residual_pair_average_bound residual 1 3
  have identity : twoDipoleExternalCenterCorrection external residual firstCenter secondCenter firstSeparation secondSeparation =
      (externalPairAverage external firstCenter firstSeparation - externalPairAverage external secondCenter secondSeparation) +
        ((residual 0 + residual 2) / 2 - (residual 1 + residual 3) / 2) := by
    dsimp [twoDipoleExternalCenterCorrection]
    ring
  rw [identity]
  have triangle := norm_add_le (externalPairAverage external firstCenter firstSeparation - externalPairAverage external secondCenter secondSeparation)
    ((residual 0 + residual 2) / 2 - (residual 1 + residual 3) / 2)
  have residualControl := norm_sub_le ((residual 0 + residual 2) / 2) ((residual 1 + residual 3) / 2)
  linarith

end EulerNonuniqueness.Section6
