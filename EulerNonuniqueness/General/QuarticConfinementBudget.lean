import EulerNonuniqueness.General.QuarticMaterialScaleChoice

namespace EulerNonuniqueness.General

theorem exists_uniform_quartic_shape_confinement_root
    {forcingConstant neutralConstant shapeConstant terminal shapeTolerance : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (neutralNonnegative : 0 ≤ neutralConstant)
    (shapeNonnegative : 0 ≤ shapeConstant) (terminalNonnegative : 0 ≤ terminal)
    (tolerancePositive : 0 < shapeTolerance) :
    ∃ rootMin ≥ (8 : ℝ), ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
      ∀ frequency weight : ℝ, 1 ≤ frequency → 0 ≤ weight →
      weight ≤ forcingConstant * frequency →
      let strength := scaleRoot ^ 3 * frequency ^ 4
      let radius := (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)
      0 < radius ∧ radius ≤ 1 ∧ weight / strength ≤ radius / 8 ∧
        shapeConstant * (neutralConstant * (strength * radius ^ 2 + weight * radius) * terminal + radius) <
          shapeTolerance := by
  let coefficient := shapeConstant *
    (neutralConstant * ((forcingConstant + 1) ^ 2 + forcingConstant * (forcingConstant + 1)) * terminal +
      (forcingConstant + 1))
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  obtain ⟨rootMin, rootStrict⟩ := exists_gt
    (max (max 8 (forcingConstant + 1)) (coefficient / shapeTolerance))
  have rootEight : 8 < rootMin :=
    (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt rootStrict
  have rootCoefficient : forcingConstant + 1 < rootMin :=
    (le_trans (le_max_right _ _) (le_max_left _ _)).trans_lt rootStrict
  have rootBudget : coefficient / shapeTolerance < rootMin :=
    (le_max_right _ _).trans_lt rootStrict
  refine ⟨rootMin, rootEight.le, ?_⟩
  intro scaleRoot rootLarge frequency weight frequencyLarge weightNonnegative weightBound
  have rootPositive : 0 < scaleRoot := by linarith
  have rootOne : 1 ≤ scaleRoot := by linarith
  have rootSquare : scaleRoot ≤ scaleRoot ^ 2 := by nlinarith
  have frequencyPositive : 0 < frequency := by linarith
  have frequencySquare : 1 ≤ frequency ^ 2 := by nlinarith
  have denominatorLarge : scaleRoot ≤ scaleRoot ^ 2 * frequency ^ 2 :=
    rootSquare.trans (le_mul_of_one_le_right (sq_nonneg scaleRoot) frequencySquare)
  have radiusBound : (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) ≤
      (forcingConstant + 1) / scaleRoot :=
    div_le_div_of_nonneg_left (by linarith) rootPositive denominatorLarge
  have radiusSmall : (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) ≤ 1 :=
    radiusBound.trans ((div_le_one₀ rootPositive).mpr (rootCoefficient.le.trans rootLarge))
  have primitiveBound : weight / (scaleRoot ^ 3 * frequency ^ 4) ≤
      ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) / 8 :=
    (div_le_div_of_nonneg_right weightBound (by positivity)).trans
      (quartic_frequency_primitive_small forcingNonnegative (rootEight.le.trans rootLarge) frequencyLarge)
  have forcingBound : weight * ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) ≤
      forcingConstant * (forcingConstant + 1) / scaleRoot :=
    (mul_le_mul_of_nonneg_right weightBound (by positivity)).trans
      (quartic_frequency_quadratic_forcing_ratio forcingNonnegative (by linarith) rootOne frequencyLarge)
  have cubicIdentity := quartic_frequency_cubic_ratio
    (radiusCoefficient := forcingConstant + 1) rootPositive.ne' frequencyPositive.ne'
  have totalBound : shapeConstant *
      (neutralConstant *
        ((scaleRoot ^ 3 * frequency ^ 4) * ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) ^ 2 +
          weight * ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2))) * terminal +
        ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2))) ≤ coefficient / scaleRoot := by
    rw [cubicIdentity]
    calc
      _ ≤ shapeConstant *
          (neutralConstant * ((forcingConstant + 1) ^ 2 / scaleRoot +
              forcingConstant * (forcingConstant + 1) / scaleRoot) * terminal +
            (forcingConstant + 1) / scaleRoot) := by gcongr
      _ = coefficient / scaleRoot := by dsimp only [coefficient]; ring
  have finalBudget : coefficient / scaleRoot < shapeTolerance := by
    apply (div_lt_iff₀ rootPositive).mpr
    have large := (div_lt_iff₀ tolerancePositive).mp (rootBudget.trans_le rootLarge)
    simpa only [mul_comm] using large
  exact ⟨by positivity, radiusSmall, primitiveBound, totalBound.trans_lt finalBudget⟩

end EulerNonuniqueness.General
