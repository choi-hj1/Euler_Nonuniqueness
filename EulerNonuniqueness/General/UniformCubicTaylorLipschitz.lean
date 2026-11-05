import EulerNonuniqueness.General.CubicTaylorCentralDifference

namespace EulerNonuniqueness.General

noncomputable section

set_option maxHeartbeats 1000000

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem quadratic_diagonal_difference_le_of_uniform_cubic
    (function : Domain → Range) (linear : Domain → Domain →L[ℝ] Range)
    (quadratic : Domain → Domain →L[ℝ] Domain →L[ℝ] Range)
    (first second direction : Domain) {constant incrementRadius : ℝ} (nonnegative : 0 ≤ constant)
    (firstTaylor : ∀ increment, ‖increment‖ ≤ incrementRadius →
      ‖cubicTaylorError function linear quadratic first increment‖ ≤ constant * ‖increment‖ ^ 3)
    (secondTaylor : ∀ increment, ‖increment‖ ≤ incrementRadius →
      ‖cubicTaylorError function linear quadratic second increment‖ ≤ constant * ‖increment‖ ^ 3)
    (close : 2 * ‖second - first‖ ≤ incrementRadius) (directionBound : ‖direction‖ ≤ 2) :
    ‖(quadratic second - quadratic first) direction direction‖ ≤ 40 * constant * ‖second - first‖ := by
  by_cases equal : first = second
  · subst second
    simp
  let distance := ‖second - first‖
  have distancePositive : 0 < distance := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm equal))
  have distanceNonnegative : 0 ≤ distance := le_of_lt distancePositive
  let step := (distance / 2) • direction
  have stepBound : ‖step‖ ≤ distance := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ distance / 2)]
    nlinarith
  have differenceNorm : ‖second - first‖ = distance := rfl
  have plusBound : ‖(second - first) + step‖ ≤ 2 * distance :=
    (norm_add_le _ _).trans (by rw [differenceNorm]; linarith)
  have minusBound : ‖(second - first) - step‖ ≤ 2 * distance :=
    (norm_sub_le _ _).trans (by rw [differenceNorm]; linarith)
  have distanceSmall : distance ≤ incrementRadius := by dsimp only [distance]; nlinarith [norm_nonneg (second - first)]
  have firstPlus : ‖cubicTaylorError function linear quadratic first ((second - first) + step)‖ ≤
      constant * (2 * distance) ^ 3 :=
    (firstTaylor _ (plusBound.trans close)).trans (by gcongr)
  have firstMinus : ‖cubicTaylorError function linear quadratic first ((second - first) - step)‖ ≤
      constant * (2 * distance) ^ 3 :=
    (firstTaylor _ (minusBound.trans close)).trans (by gcongr)
  have firstCenter : ‖cubicTaylorError function linear quadratic first (second - first)‖ ≤
      constant * distance ^ 3 := firstTaylor _ distanceSmall
  have secondPlus : ‖cubicTaylorError function linear quadratic second step‖ ≤ constant * distance ^ 3 :=
    (secondTaylor _ (stepBound.trans distanceSmall)).trans (by gcongr)
  have secondMinus : ‖cubicTaylorError function linear quadratic second (-step)‖ ≤ constant * distance ^ 3 := by
    have negativeBound : ‖-step‖ ≤ distance := by simpa only [norm_neg] using stepBound
    exact (secondTaylor _ (negativeBound.trans distanceSmall)).trans (by gcongr)
  have centralBound : ‖(2 : ℝ) • ((quadratic second - quadratic first) step step)‖ ≤
      20 * constant * distance ^ 3 := by
    rw [cubicTaylorError_central_identity function linear quadratic first second step]
    have triangle := norm_five_term_difference_le
      (cubicTaylorError function linear quadratic first ((second - first) + step))
      (cubicTaylorError function linear quadratic first ((second - first) - step))
      (cubicTaylorError function linear quadratic first (second - first))
      (cubicTaylorError function linear quadratic second step)
      (cubicTaylorError function linear quadratic second (-step))
    nlinarith
  have scaledValue : (quadratic second - quadratic first) step step =
      (distance / 2) ^ 2 • ((quadratic second - quadratic first) direction direction) := by
    simp only [step, map_smul, ContinuousLinearMap.smul_apply, smul_smul, pow_two]
  rw [scaledValue, smul_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * (distance / 2) ^ 2)] at centralBound
  have coefficient : (2 : ℝ) * (distance / 2) ^ 2 = distance ^ 2 / 2 := by ring
  rw [coefficient] at centralBound
  have rightIdentity : 20 * constant * distance ^ 3 = (distance ^ 2 / 2) * (40 * constant * distance) := by ring
  rw [rightIdentity] at centralBound
  exact (mul_le_mul_left (by positivity : 0 < distance ^ 2 / 2)).mp centralBound

theorem quadratic_operator_difference_le_of_uniform_cubic
    (function : Domain → Range) (linear : Domain → Domain →L[ℝ] Range)
    (quadratic : Domain → Domain →L[ℝ] Domain →L[ℝ] Range)
    (first second : Domain) {constant incrementRadius : ℝ} (nonnegative : 0 ≤ constant)
    (firstSymmetric : ∀ left right, quadratic first left right = quadratic first right left)
    (secondSymmetric : ∀ left right, quadratic second left right = quadratic second right left)
    (firstTaylor : ∀ increment, ‖increment‖ ≤ incrementRadius →
      ‖cubicTaylorError function linear quadratic first increment‖ ≤ constant * ‖increment‖ ^ 3)
    (secondTaylor : ∀ increment, ‖increment‖ ≤ incrementRadius →
      ‖cubicTaylorError function linear quadratic second increment‖ ≤ constant * ‖increment‖ ^ 3)
    (close : 2 * ‖second - first‖ ≤ incrementRadius) :
    ‖quadratic second - quadratic first‖ ≤ 20 * constant * ‖second - first‖ := by
  have symmetric (left right : Domain) : (quadratic second - quadratic first) left right =
      (quadratic second - quadratic first) right left := by
    simp only [ContinuousLinearMap.sub_apply, secondSymmetric left right, firstSymmetric left right]
  have actual := bilinear_opNorm_le_of_diagonal_ball_two (quadratic second - quadratic first)
    (by positivity : 0 ≤ 40 * constant * ‖second - first‖) symmetric
    (fun direction bounded => quadratic_diagonal_difference_le_of_uniform_cubic function linear quadratic
      first second direction nonnegative firstTaylor secondTaylor close bounded)
  exact actual.trans_eq (by ring)

end

end EulerNonuniqueness.General
