import EulerNonuniqueness.Section6.PaperInitialMomentAbsorption

noncomputable section

namespace EulerNonuniqueness.Section6

theorem residualDipole_moment_ramp_rate_bound
    {frequency length distance horizon initialError forcing : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length)
    (distanceLarge : 2048 ≤ distance) (initialErrorSmall : initialError ≤ 1 / 1024)
    (relativeSmall : forcing * horizon ≤ 1 / 4096)
    (centerSmall : forcing * distance / frequency ≤ 1 / 4096) :
    20 * frequency * length ^ 2 * initialError + 83200 * frequency * length ^ 2 / distance ^ 2 +
      76 * frequency * forcing * length ^ 2 * horizon + 36 * forcing * length ^ 2 * distance ≤
        frequency * length ^ 2 / 8 := by
  have distancePositive : 0 < distance := by linarith
  have inverseSquare : 83200 / distance ^ 2 ≤ (1 / 32 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos distancePositive)).mpr
    nlinarith
  have normalized : 20 * initialError + 83200 / distance ^ 2 + 76 * (forcing * horizon) +
      36 * (forcing * distance / frequency) ≤ (1 / 8 : ℝ) := by linarith
  have multiplied := mul_le_mul_of_nonneg_left normalized (show 0 ≤ frequency * length ^ 2 by positivity)
  convert multiplied using 1
  · field_simp [frequencyPositive.ne']
    <;> ring
  · ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem Scales.moment_ramp_weighted_cost_absorption (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {distance outgoingRadius horizon initialError forcing deformation : ℝ}
    (distancePositive : 0 < distance) (ratioLarge : 1024 ≤ scales.ratio)
    (outgoingRadiusLarge : 2048 ≤ outgoingRadius) (initialErrorSmall : initialError ≤ 1 / 1024)
    (relativeSmall : forcing * horizon ≤ 1 / 4096)
    (centerSmall : forcing * outgoingRadius / scales.omega (index + 1) ≤ 1 / 4096)
    (radiusSmall : scales.radius (index + 1) ≤ scales.length (index + 1))
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16) :
    let rate := 20 * scales.omega (index + 1) * scales.length (index + 1) ^ 2 * initialError +
      83200 * scales.omega (index + 1) * scales.length (index + 1) ^ 2 / outgoingRadius ^ 2 +
      76 * scales.omega (index + 1) * forcing * scales.length (index + 1) ^ 2 * horizon +
      36 * forcing * scales.length (index + 1) ^ 2 * outgoingRadius
    let decay := 2 * Real.sqrt 2 * scales.omega index
    (6 / (Real.pi * distance ^ 4)) *
      (scales.circulation (index + 1) * rate / decay ^ 2 +
        1024 * scales.circulation (index + 1) * scales.radius (index + 1) ^ 2 * deformation / decay) ≤
      (1 / 4 : ℝ) * (Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)) := by
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index
  have sourcePositive := scales.omega_pos frequencyPositive ratioPositive (index + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have lengthPositive := scales.length_pos (index + 1)
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtTwoFourth : Real.sqrt 2 ^ 4 = 4 := by
    calc
      _ = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have sqrtThreeLower : 3 / 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have rateBound := Section6.residualDipole_moment_ramp_rate_bound sourcePositive lengthPositive
    outgoingRadiusLarge initialErrorSmall relativeSmall centerSmall
  have radiusSquare : scales.radius (index + 1) ^ 2 ≤ scales.length (index + 1) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) lengthPositive.le).mpr radiusSmall
  have deformationBound : scales.radius (index + 1) ^ 2 * deformation ≤ scales.length (index + 1) ^ 2 / 16 := by
    calc
      _ ≤ scales.length (index + 1) ^ 2 * (1 / 16) := by gcongr
      _ = _ := by ring
  have firstCoefficient : (3 / 64 : ℝ) ≤ Real.sqrt 3 / (16 * Real.sqrt 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * Real.sqrt 2)).mpr
    nlinarith
  have ratioCoefficient : 96 / scales.ratio ≤ Real.sqrt 3 / 16 := by
    apply (div_le_iff₀ ratioPositive).mpr
    nlinarith [mul_le_mul_of_nonneg_right sqrtThreeLower ratioPositive.le]
  have secondCoefficient : 96 / (Real.sqrt 2 * scales.ratio) ≤ Real.sqrt 3 / (16 * Real.sqrt 2) := by
    convert div_le_div_of_nonneg_right ratioCoefficient sqrtTwoPositive.le using 1 <;> ring
  have coefficientBound : (3 / 64 : ℝ) + 96 / (Real.sqrt 2 * scales.ratio) ≤ Real.sqrt 3 / (8 * Real.sqrt 2) := by
    calc
      _ ≤ Real.sqrt 3 / (16 * Real.sqrt 2) + Real.sqrt 3 / (16 * Real.sqrt 2) :=
        add_le_add firstCoefficient secondCoefficient
      _ = _ := by ring
  let common := scales.circulation (index + 1) ^ 2 /
    (Real.pi ^ 2 * scales.omega index ^ 2 * distance ^ 4)
  have commonNonnegative : 0 ≤ common := by dsimp only [common]; positivity
  have omegaNext : scales.omega (index + 1) = scales.ratio * scales.omega index := by
    simp only [Scales.omega, pow_succ]
    ring
  dsimp only
  calc
    _ ≤ (6 / (Real.pi * distance ^ 4)) *
        (scales.circulation (index + 1) * (scales.omega (index + 1) * scales.length (index + 1) ^ 2 / 8) /
            (2 * Real.sqrt 2 * scales.omega index) ^ 2 +
          1024 * scales.circulation (index + 1) * (scales.length (index + 1) ^ 2 / 16) /
            (2 * Real.sqrt 2 * scales.omega index)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 6 / (Real.pi * distance ^ 4))
      apply add_le_add
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left rateBound circulationPositive.le) (sq_nonneg _)
      · have multiplied := mul_le_mul_of_nonneg_left deformationBound
          (show 0 ≤ 1024 * scales.circulation (index + 1) by positivity)
        convert div_le_div_of_nonneg_right multiplied
          (show 0 ≤ 2 * Real.sqrt 2 * scales.omega index by positivity) using 1 <;> ring
    _ = ((3 / 64 : ℝ) + 96 / (Real.sqrt 2 * scales.ratio)) * common := by
      dsimp only [common]
      simp only [Scales.circulation, omegaNext]
      field_simp [Real.pi_ne_zero, distancePositive.ne', sqrtTwoPositive.ne', receiverPositive.ne', ratioPositive.ne']
      ring_nf
      simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrtTwoFourth]
      <;> ring
    _ ≤ (Real.sqrt 3 / (8 * Real.sqrt 2)) * common :=
      mul_le_mul_of_nonneg_right coefficientBound commonNonnegative
    _ = _ := by dsimp only [common]; ring

end EulerNonuniqueness.Paper
