import EulerNonuniqueness.Section6.FourPointShapeReduction

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

def pointShapeRatio (positive negative : ℂ) : ℝ := ‖negative‖ ^ 2 / ‖positive‖ ^ 2

def pointShapeAngle (positive negative : ℂ) : ℝ :=
  unwrappedShapeArgument ((negative / positive) ^ 2)

def pointShapeChart (positive negative : ℂ) : ℝ × ℝ :=
  shapeChart (pointShapeRatio positive negative) (pointShapeAngle positive negative)

def localPointShapeChart (positive negative : ℝ → ℂ) (baseTime currentTime : ℝ) : ℝ × ℝ :=
  shapeChart (pointShapeRatio (positive currentTime) (negative currentTime))
    (localShapePhase ((negative baseTime / positive baseTime) ^ 2)
      (fun time => (negative time / positive time) ^ 2) currentTime)

def pointShapeForcing (positive negative positiveForcing negativeForcing : ℂ) : ℝ × ℝ :=
  let difference := negativeForcing / negative - positiveForcing / positive
  ((2 * pointShapeRatio positive negative * difference.re / rhombusRatio +
      2 * difference.im / Real.sqrt 2) / 2,
    (2 * pointShapeRatio positive negative * difference.re / rhombusRatio -
      2 * difference.im / Real.sqrt 2) / 2)

theorem localPointShapeChart_at_base {positive negative : ℝ → ℂ} {time : ℝ}
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0) :
    localPointShapeChart positive negative time time = pointShapeChart (positive time) (negative time) := by
  unfold localPointShapeChart pointShapeChart pointShapeAngle
  congr 1
  exact localShapePhase_at_reference (field := fun current => (negative current / positive current) ^ 2)
    (pow_ne_zero 2 (div_ne_zero negativeNonzero positiveNonzero))

theorem shapeChart_forced_hasDerivAt {ratio angle : ℝ → ℝ} {frequency time radialForcing angularForcing : ℝ}
    (radialEquation : HasDerivAt ratio
      (radialVelocity frequency (ratio time) (angle time) + radialForcing) time)
    (angularEquation : HasDerivAt angle
      (shapeAngleVelocity frequency (ratio time) (angle time) + angularForcing) time) :
    HasDerivAt (fun current => shapeChart (ratio current) (angle current))
      (shapeChartVelocity frequency (shapeChart (ratio time) (angle time)) +
        ((radialForcing / rhombusRatio + angularForcing / Real.sqrt 2) / 2,
          (radialForcing / rhombusRatio - angularForcing / Real.sqrt 2) / 2)) time := by
  have horizontal := (radialEquation.div_const rhombusRatio).sub_const 1
  have vertical := (angularEquation.sub_const Real.pi).div_const (Real.sqrt 2)
  have first := (horizontal.add vertical).div_const 2
  have second := (horizontal.sub vertical).div_const 2
  have paired := first.prodMk second
  convert paired using 1
  dsimp [shapeChartVelocity, Prod.add_def]
  rw [(shapeChart_reconstruction (ratio time) (angle time)).1,
    (shapeChart_reconstruction (ratio time) (angle time)).2]
  apply Prod.ext <;> dsimp <;> ring

theorem localPointShapeChart_forced_equation (coefficient : ℝ) {positive negative : ℝ → ℂ}
    {positiveForcing negativeForcing : ℂ} {time : ℝ}
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0)
    (squaresNonzero : star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0)
    (normOrder : ‖negative time‖ < ‖positive time‖)
    (positiveDerivative : HasDerivAt positive
      (positivePointVelocity coefficient (positive time) (negative time) + positiveForcing) time)
    (negativeDerivative : HasDerivAt negative
      (negativePointVelocity coefficient (positive time) (negative time) + negativeForcing) time) :
    HasDerivAt (localPointShapeChart positive negative time)
      (shapeChartVelocity (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
          (pointShapeChart (positive time) (negative time)) +
        pointShapeForcing (positive time) (negative time) positiveForcing negativeForcing) time := by
  have raw := four_point_forced_shape_derivatives coefficient positiveNonzero negativeNonzero
    squaresNonzero normOrder positiveDerivative negativeDerivative
  dsimp only at raw
  have periodic := shape_velocities_unwrapped_argument
    (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
    (‖negative time‖ ^ 2 / ‖positive time‖ ^ 2) ((negative time / positive time) ^ 2)
  have phaseAt := localShapePhase_at_reference
    (field := fun current => (negative current / positive current) ^ 2)
    (pow_ne_zero 2 (div_ne_zero negativeNonzero positiveNonzero))
  have radial := raw.1
  rw [← periodic.1, ← phaseAt] at radial
  have angularRaw := raw.2.1
  rw [← periodic.2.1] at angularRaw
  have angular : HasDerivAt
      (localShapePhase ((negative time / positive time) ^ 2)
        (fun current => (negative current / positive current) ^ 2))
      (shapeAngleVelocity (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
          (‖negative time‖ ^ 2 / ‖positive time‖ ^ 2)
          (unwrappedShapeArgument ((negative time / positive time) ^ 2)) +
        2 * (negativeForcing / negative time - positiveForcing / positive time).im) time := by
    convert angularRaw.const_add
      (unwrappedShapeArgument ((negative time / positive time) ^ 2) -
        Complex.arg ((negative time / positive time) ^ 2)) using 1
    funext current
    unfold localShapePhase localComplexPhase
    ring
  rw [← phaseAt] at angular
  have chart := shapeChart_forced_hasDerivAt radial angular
  simpa only [localPointShapeChart, pointShapeChart, pointShapeForcing, pointShapeRatio,
    pointShapeAngle, phaseAt] using chart

theorem pointShapeForcing_rhombus {positive : ℂ} (positiveNonzero : positive ≠ 0) (strain : ℂ) :
    pointShapeForcing positive (Complex.I * (Real.sqrt rhombusRatio : ℂ) * positive)
      (strain * star positive)
      (strain * star (Complex.I * (Real.sqrt rhombusRatio : ℂ) * positive)) =
    (-2 * (strain * star positive / positive).re - Real.sqrt 2 * (strain * star positive / positive).im,
      -2 * (strain * star positive / positive).re + Real.sqrt 2 * (strain * star positive / positive).im) := by
  have radiusPositive := Real.sqrt_pos.mpr rhombusRatio_pos
  have radiusNonzero : (Real.sqrt rhombusRatio : ℂ) ≠ 0 := by exact_mod_cast radiusPositive.ne'
  have normIdentity : pointShapeRatio positive (Complex.I * (Real.sqrt rhombusRatio : ℂ) * positive) =
      rhombusRatio := by
    unfold pointShapeRatio
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos radiusPositive]
    have positiveNormNonzero := pow_ne_zero 2 (norm_ne_zero_iff.mpr positiveNonzero)
    rw [one_mul, mul_pow, Real.sq_sqrt rhombusRatio_pos.le]
    exact mul_div_cancel_right₀ rhombusRatio positiveNormNonzero
  have negativeLogarithm :
      strain * star (Complex.I * (Real.sqrt rhombusRatio : ℂ) * positive) /
        (Complex.I * (Real.sqrt rhombusRatio : ℂ) * positive) =
      -(strain * star positive / positive) := by
    simp only [star_mul, Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    field_simp
    ring
  unfold pointShapeForcing
  rw [normIdentity, negativeLogarithm]
  dsimp
  have sqrtTwoNonzero := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  apply Prod.ext <;> dsimp <;> field_simp [rhombusRatio_pos.ne', sqrtTwoNonzero] <;>
    ring_nf <;> simp [Real.sq_sqrt] <;> ring

theorem four_point_impulse_conserved (coefficient : ℝ) {positive negative : ℝ → ℂ}
    (positiveNonzero : ∀ time, positive time ≠ 0) (negativeNonzero : ∀ time, negative time ≠ 0)
    (squaresNonzero : ∀ time, star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0)
    (normOrder : ∀ time, ‖negative time‖ < ‖positive time‖)
    (positiveDerivative : ∀ time, HasDerivAt positive
      (positivePointVelocity coefficient (positive time) (negative time)) time)
    (negativeDerivative : ∀ time, HasDerivAt negative
      (negativePointVelocity coefficient (positive time) (negative time)) time)
    (firstTime secondTime : ℝ) :
    ‖positive firstTime‖ ^ 2 - ‖negative firstTime‖ ^ 2 =
      ‖positive secondTime‖ ^ 2 - ‖negative secondTime‖ ^ 2 := by
  have derivative := fun time => four_point_impulse_hasDerivAt coefficient
    (positiveNonzero time) (negativeNonzero time) (squaresNonzero time) (normOrder time)
    (positiveDerivative time) (negativeDerivative time)
  exact is_const_of_deriv_eq_zero (fun time => (derivative time).differentiableAt)
    (fun time => (derivative time).deriv) firstTime secondTime

end EulerNonuniqueness.Section6
