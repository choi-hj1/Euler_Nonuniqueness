import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem triangular_neutral_response_le_of_small_feedback
    {constant tolerance centered moment scaledRaw dilationRate dilation phase shape forcing : ℝ}
    (constantOne : 1 ≤ constant) (toleranceNonnegative : 0 ≤ tolerance)
    (smallFeedback : 28 * constant ^ 3 * tolerance ≤ 1)
    (centeredNonnegative : 0 ≤ centered) (shapeNonnegative : 0 ≤ shape)
    (forcingNonnegative : 0 ≤ forcing)
    (rawBound : scaledRaw ≤ tolerance * centered + constant * forcing)
    (momentBound : moment ≤ tolerance * (centered + scaledRaw) + constant * forcing)
    (velocityBound : dilationRate ≤ tolerance * moment + tolerance * centered +
      constant * scaledRaw + constant * forcing)
    (dilationBound : dilation ≤ dilationRate)
    (phaseBound : phase ≤ constant * dilationRate + tolerance * moment +
      tolerance * centered + tolerance * shape + constant * scaledRaw + constant * forcing)
    (reconstruction : centered ≤ tolerance * moment + constant * (dilation + shape + phase)) :
    centered ≤ 4 * constant * shape + 28 * constant ^ 4 * forcing := by
  have constantNonnegative : 0 ≤ constant := le_trans (by norm_num) constantOne
  have cubeOne : 1 ≤ constant ^ 3 := one_le_pow₀ constantOne
  have constantSquare : constant ≤ constant ^ 2 := by nlinarith only [constantOne]
  have squareCube : constant ^ 2 ≤ constant ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg constant) (sub_nonneg.mpr constantOne)]
  have cubeFourth : constant ^ 3 ≤ constant ^ 4 := by
    nlinarith only [mul_nonneg (pow_nonneg constantNonnegative 3) (sub_nonneg.mpr constantOne)]
  have toleranceCube := mul_le_mul_of_nonneg_right cubeOne toleranceNonnegative
  have toleranceOne : tolerance ≤ 1 := by linarith only [smallFeedback, toleranceCube, toleranceNonnegative]
  have toleranceSquare : tolerance ^ 2 ≤ tolerance := by nlinarith only [toleranceNonnegative, toleranceOne]
  have constantTolerance : tolerance ≤ constant * tolerance := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr constantOne) toleranceNonnegative]
  have squareTolerance : constant * tolerance ≤ constant ^ 2 * tolerance :=
    mul_le_mul_of_nonneg_right constantSquare toleranceNonnegative
  have cubeTolerance : constant ^ 2 * tolerance ≤ constant ^ 3 * tolerance :=
    mul_le_mul_of_nonneg_right squareCube toleranceNonnegative
  have constantToleranceUpper : constant * tolerance ≤ constant := by
    nlinarith only [mul_nonneg constantNonnegative (sub_nonneg.mpr toleranceOne)]
  have momentEstimate : moment ≤ 2 * tolerance * centered + 2 * constant * forcing := by
    have multiplied := mul_le_mul_of_nonneg_left rawBound toleranceNonnegative
    have first : moment ≤ tolerance * (1 + tolerance) * centered +
        constant * (1 + tolerance) * forcing := by linarith only [momentBound, multiplied]
    have centerCoefficient : tolerance * (1 + tolerance) ≤ 2 * tolerance := by linarith only [toleranceSquare]
    have forceCoefficient : constant * (1 + tolerance) ≤ 2 * constant := by linarith only [constantToleranceUpper]
    exact first.trans (add_le_add
      (mul_le_mul_of_nonneg_right centerCoefficient centeredNonnegative)
      (mul_le_mul_of_nonneg_right forceCoefficient forcingNonnegative))
  have velocityEstimate : dilationRate ≤
      4 * constant * tolerance * centered + 4 * constant ^ 2 * forcing := by
    have momentMultiplied := mul_le_mul_of_nonneg_left momentEstimate toleranceNonnegative
    have rawMultiplied := mul_le_mul_of_nonneg_left rawBound constantNonnegative
    have first : dilationRate ≤ (2 * tolerance ^ 2 + tolerance + constant * tolerance) * centered +
        (2 * constant * tolerance + constant ^ 2 + constant) * forcing := by
      linarith only [velocityBound, momentMultiplied, rawMultiplied]
    have centerCoefficient : 2 * tolerance ^ 2 + tolerance + constant * tolerance ≤
        4 * constant * tolerance := by linarith only [toleranceSquare, constantTolerance]
    have forceCoefficient : 2 * constant * tolerance + constant ^ 2 + constant ≤
        4 * constant ^ 2 := by linarith only [constantToleranceUpper, constantSquare]
    exact first.trans (add_le_add
      (mul_le_mul_of_nonneg_right centerCoefficient centeredNonnegative)
      (mul_le_mul_of_nonneg_right forceCoefficient forcingNonnegative))
  have phaseEstimate : phase ≤ 8 * constant ^ 2 * tolerance * centered +
      8 * constant ^ 3 * forcing + tolerance * shape := by
    have velocityMultiplied := mul_le_mul_of_nonneg_left velocityEstimate constantNonnegative
    have momentMultiplied := mul_le_mul_of_nonneg_left momentEstimate toleranceNonnegative
    have rawMultiplied := mul_le_mul_of_nonneg_left rawBound constantNonnegative
    have first : phase ≤
        (4 * constant ^ 2 * tolerance + 2 * tolerance ^ 2 + tolerance + constant * tolerance) * centered +
        (4 * constant ^ 3 + 2 * constant * tolerance + constant ^ 2 + constant) * forcing +
        tolerance * shape := by
      linarith only [phaseBound, velocityMultiplied, momentMultiplied, rawMultiplied]
    have centerCoefficient : 4 * constant ^ 2 * tolerance + 2 * tolerance ^ 2 + tolerance +
        constant * tolerance ≤ 8 * constant ^ 2 * tolerance := by
      linarith only [toleranceSquare, constantTolerance, squareTolerance]
    have forceCoefficient : 4 * constant ^ 3 + 2 * constant * tolerance + constant ^ 2 + constant ≤
        8 * constant ^ 3 := by linarith only [constantToleranceUpper, constantSquare, squareCube]
    exact first.trans (add_le_add_right (add_le_add
      (mul_le_mul_of_nonneg_right centerCoefficient centeredNonnegative)
      (mul_le_mul_of_nonneg_right forceCoefficient forcingNonnegative)) _)
  have reconstructed : centered ≤
      14 * constant ^ 3 * tolerance * centered + 2 * constant * shape +
        14 * constant ^ 4 * forcing := by
    have momentMultiplied := mul_le_mul_of_nonneg_left momentEstimate toleranceNonnegative
    have velocityMultiplied := mul_le_mul_of_nonneg_left velocityEstimate constantNonnegative
    have dilationMultiplied := mul_le_mul_of_nonneg_left dilationBound constantNonnegative
    have phaseMultiplied := mul_le_mul_of_nonneg_left phaseEstimate constantNonnegative
    have first : centered ≤
        (2 * tolerance ^ 2 + 4 * constant ^ 2 * tolerance + 8 * constant ^ 3 * tolerance) * centered +
        (constant + constant * tolerance) * shape +
        (2 * constant * tolerance + 4 * constant ^ 3 + 8 * constant ^ 4) * forcing := by
      linarith only [reconstruction, momentMultiplied, velocityMultiplied, dilationMultiplied, phaseMultiplied]
    have centerCoefficient : 2 * tolerance ^ 2 + 4 * constant ^ 2 * tolerance +
        8 * constant ^ 3 * tolerance ≤ 14 * constant ^ 3 * tolerance := by
      linarith only [toleranceSquare, constantTolerance, squareTolerance, cubeTolerance]
    have shapeCoefficient : constant + constant * tolerance ≤ 2 * constant := by linarith only [constantToleranceUpper]
    have forceCoefficient : 2 * constant * tolerance + 4 * constant ^ 3 +
        8 * constant ^ 4 ≤ 14 * constant ^ 4 := by
      linarith only [constantToleranceUpper, constantSquare, squareCube, cubeFourth]
    exact first.trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right centerCoefficient centeredNonnegative)
      (mul_le_mul_of_nonneg_right shapeCoefficient shapeNonnegative))
      (mul_le_mul_of_nonneg_right forceCoefficient forcingNonnegative))
  have absorption := mul_le_mul_of_nonneg_right smallFeedback centeredNonnegative
  linarith only [reconstructed, absorption]

end EulerNonuniqueness.General
