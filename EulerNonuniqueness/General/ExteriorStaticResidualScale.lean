import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

def exteriorStaticResidualScaleModel
    (frequency constant epsilon radius ratio transverse angular : ℝ) : ℝ :=
  frequency * ((2 * constant * epsilon) * (constant * epsilon * (transverse + angular)) +
    (constant * (transverse + angular)) * (constant * epsilon) ^ 2) +
  (constant * frequency * epsilon) * ((2 * constant * radius) * (constant * (transverse + radius * angular)) +
    (constant * angular) * (2 * constant * radius) ^ 2) +
  (constant * frequency * epsilon * ratio) *
    (constant * (transverse + radius * angular) + (constant * angular) * (constant * radius)) +
  frequency * ((constant * radius) * (constant * epsilon * ratio * angular) +
    (constant * (transverse + radius * angular) + (constant * angular) * (constant * radius)) *
      (constant * epsilon * ratio)) +
  frequency⁻¹ * ((constant * frequency * epsilon) *
    ((2 * constant * frequency * epsilon) * (constant * (transverse + angular))) +
    ((constant * frequency * epsilon) * (constant * angular)) * (constant * frequency * epsilon))

theorem exteriorStaticResidualScaleModel_polynomial
    {frequency : ℝ} (nonzero : frequency ≠ 0) (constant epsilon radius ratio transverse angular : ℝ) :
    exteriorStaticResidualScaleModel frequency constant epsilon radius ratio transverse angular =
      frequency *
        ((2 * constant ^ 2 + 3 * constant ^ 3) * epsilon ^ 2 * transverse +
          (2 * constant ^ 2 + 4 * constant ^ 3) * epsilon ^ 2 * angular +
          (2 * constant ^ 3) * epsilon * radius * transverse +
          (2 * constant ^ 3 + 4 * constant ^ 4) * epsilon * radius ^ 2 * angular +
          (2 * constant ^ 2) * epsilon * ratio * transverse +
          (3 * constant ^ 2 + 2 * constant ^ 3) * epsilon * ratio * radius * angular) := by
  unfold exteriorStaticResidualScaleModel
  field_simp
  ring

theorem exteriorStaticResidualScaleModel_le_weighted
    {frequency constant epsilon radius ratio transverse angular : ℝ}
    (frequencyPositive : 0 < frequency) (constantNonnegative : 0 ≤ constant)
    (epsilonNonnegative : 0 ≤ epsilon) (radiusNonnegative : 0 ≤ radius) (ratioNonnegative : 0 ≤ ratio)
    (transverseNonnegative : 0 ≤ transverse) (angularNonnegative : 0 ≤ angular) :
    exteriorStaticResidualScaleModel frequency constant epsilon radius ratio transverse angular ≤
      frequency * (5 * constant ^ 2 + 10 * constant ^ 3 + 4 * constant ^ 4 + 1) *
        ((epsilon ^ 2 + epsilon * radius + epsilon * ratio) * transverse +
          (epsilon ^ 2 + epsilon * radius ^ 2 + epsilon * ratio * radius) * angular) := by
  rw [exteriorStaticResidualScaleModel_polynomial frequencyPositive.ne']
  let coefficient := 5 * constant ^ 2 + 10 * constant ^ 3 + 4 * constant ^ 4 + 1
  have squareNonnegative := sq_nonneg constant
  have cubeNonnegative := pow_nonneg constantNonnegative 3
  have fourthNonnegative := pow_nonneg constantNonnegative 4
  have first : 2 * constant ^ 2 + 3 * constant ^ 3 ≤ coefficient := by dsimp only [coefficient]; nlinarith
  have second : 2 * constant ^ 2 + 4 * constant ^ 3 ≤ coefficient := by dsimp only [coefficient]; nlinarith
  have third : 2 * constant ^ 3 ≤ coefficient := by dsimp only [coefficient]; nlinarith
  have fourth : 2 * constant ^ 3 + 4 * constant ^ 4 ≤ coefficient := by dsimp only [coefficient]; nlinarith
  have fifth : 2 * constant ^ 2 ≤ coefficient := by dsimp only [coefficient]; nlinarith
  have sixth : 3 * constant ^ 2 + 2 * constant ^ 3 ≤ coefficient := by dsimp only [coefficient]; nlinarith
  have bounded := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right first (by positivity : 0 ≤ epsilon ^ 2 * transverse))
    (mul_le_mul_of_nonneg_right second (by positivity : 0 ≤ epsilon ^ 2 * angular)))
    (mul_le_mul_of_nonneg_right third (by positivity : 0 ≤ epsilon * radius * transverse)))
    (mul_le_mul_of_nonneg_right fourth (by positivity : 0 ≤ epsilon * radius ^ 2 * angular)))
    (mul_le_mul_of_nonneg_right fifth (by positivity : 0 ≤ epsilon * ratio * transverse)))
    (mul_le_mul_of_nonneg_right sixth (by positivity : 0 ≤ epsilon * ratio * radius * angular))
  have scaled := mul_le_mul_of_nonneg_left bounded frequencyPositive.le
  convert scaled using 1 <;> dsimp only [coefficient] <;> ring

theorem exteriorStaticResidualScaleModel_le_quadratic_rate
    {frequency constant epsilon radius ratio transverse angular : ℝ}
    (frequencyPositive : 0 < frequency) (constantNonnegative : 0 ≤ constant)
    (epsilonNonnegative : 0 ≤ epsilon) (radiusNonnegative : 0 ≤ radius) (radiusSmall : radius ≤ 1)
    (ratioNonnegative : 0 ≤ ratio) (transverseNonnegative : 0 ≤ transverse) (angularNonnegative : 0 ≤ angular)
    (epsilonSmall : epsilon ≤ radius) (squaredSmall : epsilon ^ 2 ≤ radius ^ 3)
    (tailSmall : epsilon * ratio ≤ radius ^ 2) :
    exteriorStaticResidualScaleModel frequency constant epsilon radius ratio transverse angular ≤
      3 * frequency * (5 * constant ^ 2 + 10 * constant ^ 3 + 4 * constant ^ 4 + 1) * radius ^ 2 *
        (transverse + radius * angular) := by
  have actual := exteriorStaticResidualScaleModel_le_weighted frequencyPositive constantNonnegative
    epsilonNonnegative radiusNonnegative ratioNonnegative transverseNonnegative angularNonnegative
  have radiusCubed : radius ^ 3 ≤ radius ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg radius) (sub_nonneg.mpr radiusSmall)]
  have linear : epsilon ^ 2 + epsilon * radius + epsilon * ratio ≤ 3 * radius ^ 2 := by
    have product := mul_le_mul_of_nonneg_right epsilonSmall radiusNonnegative
    linarith [squaredSmall.trans radiusCubed]
  have neutral : epsilon ^ 2 + epsilon * radius ^ 2 + epsilon * ratio * radius ≤ 3 * radius ^ 3 := by
    have product := mul_le_mul_of_nonneg_right epsilonSmall (sq_nonneg radius)
    have tail := mul_le_mul_of_nonneg_right tailSmall radiusNonnegative
    nlinarith
  have bounded := add_le_add
    (mul_le_mul_of_nonneg_right linear transverseNonnegative)
    (mul_le_mul_of_nonneg_right neutral angularNonnegative)
  have scaled := mul_le_mul_of_nonneg_left bounded (by positivity : 0 ≤
    frequency * (5 * constant ^ 2 + 10 * constant ^ 3 + 4 * constant ^ 4 + 1))
  exact actual.trans (scaled.trans_eq (by ring))

end EulerNonuniqueness.General
