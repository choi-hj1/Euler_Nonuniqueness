import EulerNonuniqueness.General.StationaryLipschitzSecondFactor
import EulerNonuniqueness.General.BilinearOperatorCalculus

namespace EulerNonuniqueness.General

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open Set Metric
open scoped NNReal

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_jet_remainder_transverse_factor
    (function : Space → Space) (derivative : Space → Space →L[ℝ] Space)
    (second : Space → BilinearEnd Space) (linear : Space →L[ℝ] Space) (bilinear : BilinearEnd Space)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius) (constant : ℝ≥0)
    (actualFirst : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt function (derivative value) value)
    (actualSecond : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt derivative (second value) value)
    (lipschitz : LipschitzOnWith constant second (closedBall (0 : Space) radius))
    (linearIdentity : derivative 0 = linear) (secondIdentity : second 0 = bilinear + bilinear.flip)
    (neutral relative : Space) (inside : ‖neutral‖ + ‖relative‖ ≤ radius)
    (stationary : function neutral = 0) (kernel : linear neutral = 0)
    (quadraticZero : bilinear neutral neutral = 0) :
    ‖function (neutral + relative) - linear (neutral + relative) -
      bilinear (neutral + relative) (neutral + relative)‖ ≤
      (constant : ℝ) * (‖neutral‖ + ‖relative‖) ^ 2 * ‖relative‖ := by
  let remainder := fun value => function value - linear value - bilinear value value
  let remainderDerivative := fun value => derivative value - linear - (bilinear + bilinear.flip) value
  let remainderSecond := fun value => second value - (bilinear + bilinear.flip)
  have firstActual : ∀ value ∈ closedBall (0 : Space) radius,
      HasFDerivAt remainder (remainderDerivative value) value := by
    intro value member
    have quadraticActual := (bilinear.hasFDerivAt (x := value)).clm_apply (hasFDerivAt_id value)
    simpa only [ContinuousLinearMap.comp_id, ContinuousLinearMap.add_apply] using
      ((actualFirst value member).sub (linear.hasFDerivAt (x := value))).sub quadraticActual
  have secondActual : ∀ value ∈ closedBall (0 : Space) radius,
      HasFDerivAt remainderDerivative (remainderSecond value) value := by
    intro value member
    exact ((actualSecond value member).sub_const linear).sub
      ((bilinear + bilinear.flip).hasFDerivAt (x := value))
  have remainderLipschitz : LipschitzOnWith constant remainderSecond (closedBall (0 : Space) radius) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first firstInside secondPoint secondInside
    change dist (second first - (bilinear + bilinear.flip))
      (second secondPoint - (bilinear + bilinear.flip)) ≤ _
    rw [dist_eq_norm (second first - (bilinear + bilinear.flip))
      (second secondPoint - (bilinear + bilinear.flip))]
    have identity : second first - (bilinear + bilinear.flip) -
        (second secondPoint - (bilinear + bilinear.flip)) = second first - second secondPoint := by abel
    rw [identity, ← dist_eq_norm (second first) (second secondPoint)]
    exact lipschitz.dist_le_mul first firstInside secondPoint secondInside
  have flat : remainderDerivative 0 = 0 := by
    simp [remainderDerivative, linearIdentity]
  have secondFlat : remainderSecond 0 = 0 := by simp [remainderSecond, secondIdentity]
  have zero : remainder neutral = 0 := by simp [remainder, stationary, kernel, quadraticZero]
  exact stationary_transverse_cubic_factor_of_lipschitz_second remainder remainderDerivative remainderSecond
    radiusNonnegative constant firstActual secondActual remainderLipschitz flat secondFlat neutral relative inside zero

theorem quadratic_jet_remainder_transverse_factor_of_fderiv
    (function : Space → Space) (linear : Space →L[ℝ] Space) (bilinear : BilinearEnd Space)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius) (constant : ℝ≥0)
    (regular : ∀ value ∈ closedBall (0 : Space) radius,
      DifferentiableAt ℝ function value ∧ DifferentiableAt ℝ (fderiv ℝ function) value)
    (lipschitz : LipschitzOnWith constant (fderiv ℝ (fderiv ℝ function)) (closedBall (0 : Space) radius))
    (linearIdentity : fderiv ℝ function 0 = linear)
    (secondIdentity : fderiv ℝ (fderiv ℝ function) 0 = bilinear + bilinear.flip)
    (neutral relative : Space) (inside : ‖neutral‖ + ‖relative‖ ≤ radius)
    (stationary : function neutral = 0) (kernel : linear neutral = 0)
    (quadraticZero : bilinear neutral neutral = 0) :
    ‖function (neutral + relative) - linear (neutral + relative) -
      bilinear (neutral + relative) (neutral + relative)‖ ≤
      (constant : ℝ) * (‖neutral‖ + ‖relative‖) ^ 2 * ‖relative‖ :=
  quadratic_jet_remainder_transverse_factor function (fderiv ℝ function)
    (fderiv ℝ (fderiv ℝ function)) linear bilinear radiusNonnegative constant
    (fun value member => (regular value member).1.hasFDerivAt)
    (fun value member => (regular value member).2.hasFDerivAt)
    lipschitz linearIdentity secondIdentity neutral relative inside stationary kernel quadraticZero

end

end EulerNonuniqueness.General
