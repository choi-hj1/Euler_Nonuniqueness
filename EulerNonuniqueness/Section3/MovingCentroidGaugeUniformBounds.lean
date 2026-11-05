import EulerNonuniqueness.Section3.MovingCentroidGaugeComponentBounds

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeUniformHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeUniformC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance movingGaugeUniformDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)

def FiniteContourConfiguration.movingGaugeUniformBound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap constant : ℝ) : ℝ :=
  1 + ∑ index, (configuration.radius index * constant * |configuration.movingRawNormBound centerBound shapeRadius gap index| +
    (1 + constant) * |configuration.movingRawNormBound centerBound shapeRadius gap index|)

def FiniteContourConfiguration.movingGaugeLipschitzBound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap constant : ℝ) : ℝ :=
  1 + ∑ index,
    (configuration.radius index * (constant * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
      constant * |configuration.movingRawNormBound centerBound shapeRadius gap index| +
      |configuration.density index / 2| * constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|) +
    ((1 + constant) * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
      constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|))

theorem FiniteContourConfiguration.movingGaugeUniformBound_positive {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap : ℝ)
    {constant : ℝ} (nonnegative : 0 ≤ constant) :
    0 < configuration.movingGaugeUniformBound centerBound shapeRadius gap constant := by
  have sumNonnegative : 0 ≤ ∑ index, (configuration.radius index * constant * |configuration.movingRawNormBound centerBound shapeRadius gap index| +
      (1 + constant) * |configuration.movingRawNormBound centerBound shapeRadius gap index|) := by
    apply Finset.sum_nonneg
    intro index _member
    have radiusPositive := configuration.radius_pos index
    positivity
  unfold FiniteContourConfiguration.movingGaugeUniformBound
  linarith

theorem FiniteContourConfiguration.movingGaugeLipschitzBound_positive {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap : ℝ)
    {constant : ℝ} (nonnegative : 0 ≤ constant) :
    0 < configuration.movingGaugeLipschitzBound centerBound shapeRadius gap constant := by
  have sumNonnegative : 0 ≤ ∑ index,
      (configuration.radius index * (constant * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
        constant * |configuration.movingRawNormBound centerBound shapeRadius gap index| +
        |configuration.density index / 2| * constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|) +
      ((1 + constant) * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
        constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|)) := by
    apply Finset.sum_nonneg
    intro index _member
    have radiusPositive := configuration.radius_pos index
    positivity
  unfold FiniteContourConfiguration.movingGaugeLipschitzBound
  linarith

theorem FiniteContourConfiguration.movingStateVectorField_uniform_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap constant : ℝ}
    (positive : 0 < gap) (shapeNonnegative : 0 ≤ shapeRadius)
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi))) (constantNonnegative : 0 ≤ constant)
    (derivativeBound : ∀ data ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant)
    {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap) :
    ‖configuration.movingStateVectorField state‖ ≤ configuration.movingGaugeUniformBound centerBound shapeRadius gap constant := by
  let centerTerm := fun index => configuration.radius index * constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|
  let shapeTerm := fun index => (1 + constant) * |configuration.movingRawNormBound centerBound shapeRadius gap index|
  have centerNonnegative (index : Fin count) : 0 ≤ centerTerm index := by
    dsimp only [centerTerm]
    exact mul_nonneg (mul_nonneg (configuration.radius_pos index).le constantNonnegative) (abs_nonneg _)
  have shapeNonnegativeTerm (index : Fin count) : 0 ≤ shapeTerm index := by dsimp only [shapeTerm]; positivity
  have eachLe (index : Fin count) : centerTerm index + shapeTerm index ≤ configuration.movingGaugeUniformBound centerBound shapeRadius gap constant := by
    have single := Finset.single_le_sum (fun other _ => add_nonneg (centerNonnegative other) (shapeNonnegativeTerm other)) (Finset.mem_univ index)
    change centerTerm index + shapeTerm index ≤ 1 + ∑ other, (centerTerm other + shapeTerm other)
    linarith
  have boundNonnegative := (configuration.movingGaugeUniformBound_positive centerBound shapeRadius gap constantNonnegative).le
  change max ‖(1 : ℝ)‖ (max ‖(configuration.movingStateVectorField state).2.1‖ ‖(configuration.movingStateVectorField state).2.2‖) ≤ _
  apply max_le
  · have sumNonnegative : 0 ≤ ∑ index, (centerTerm index + shapeTerm index) :=
      Finset.sum_nonneg (fun index _ => add_nonneg (centerNonnegative index) (shapeNonnegativeTerm index))
    change ‖(1 : ℝ)‖ ≤ 1 + ∑ index, (centerTerm index + shapeTerm index)
    norm_num only [norm_one]
    linarith
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg boundNonnegative).mpr
      intro index
      have actual := (configuration.movingStateVectorField_component_norm_bounds positive shapeNonnegative shapeSmall constantNonnegative derivativeBound inside index).1
      exact actual.trans ((le_add_of_nonneg_right (shapeNonnegativeTerm index)).trans (eachLe index))
    · apply (pi_norm_le_iff_of_nonneg boundNonnegative).mpr
      intro index
      have actual := (configuration.movingStateVectorField_component_norm_bounds positive shapeNonnegative shapeSmall constantNonnegative derivativeBound inside index).2
      exact actual.trans ((le_add_of_nonneg_left (centerNonnegative index)).trans (eachLe index))

theorem FiniteContourConfiguration.movingStateVectorField_lipschitzOn {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap constant : ℝ}
    (positive : 0 < gap) (centerNonnegative : 0 ≤ centerBound) (shapeNonnegative : 0 ≤ shapeRadius)
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi))) (constantNonnegative : 0 ≤ constant)
    (derivativeBound : ∀ data ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant)
    (derivativeDifference : ∀ first ∈ closedBall standardCircleBanach shapeRadius,
      ∀ second ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional first - fderiv ℝ contourCentroidFunctional second‖ ≤ constant * ‖first - second‖) :
    LipschitzOnWith ⟨configuration.movingGaugeLipschitzBound centerBound shapeRadius gap constant,
      (configuration.movingGaugeLipschitzBound_positive centerBound shapeRadius gap constantNonnegative).le⟩
      configuration.movingStateVectorField (configuration.movingStateAdmissible centerBound shapeRadius gap) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first firstInside second secondInside
  rw [dist_eq_norm (configuration.movingStateVectorField first) (configuration.movingStateVectorField second),
    dist_eq_norm first second]
  let centerTerm := fun index => configuration.radius index * (constant * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
    constant * |configuration.movingRawNormBound centerBound shapeRadius gap index| +
    |configuration.density index / 2| * constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|)
  let shapeTerm := fun index => (1 + constant) * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
    constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|
  have centerTermNonnegative (index : Fin count) : 0 ≤ centerTerm index := by
    dsimp only [centerTerm]
    have radiusPositive := configuration.radius_pos index
    positivity
  have shapeTermNonnegative (index : Fin count) : 0 ≤ shapeTerm index := by dsimp only [shapeTerm]; positivity
  have eachLe (index : Fin count) : centerTerm index + shapeTerm index ≤ configuration.movingGaugeLipschitzBound centerBound shapeRadius gap constant := by
    have single := Finset.single_le_sum (fun other _ => add_nonneg (centerTermNonnegative other) (shapeTermNonnegative other)) (Finset.mem_univ index)
    change centerTerm index + shapeTerm index ≤ 1 + ∑ other, (centerTerm other + shapeTerm other)
    linarith
  have finalNonnegative : 0 ≤ configuration.movingGaugeLipschitzBound centerBound shapeRadius gap constant * ‖first - second‖ :=
    mul_nonneg (configuration.movingGaugeLipschitzBound_positive centerBound shapeRadius gap constantNonnegative).le (norm_nonneg (first - second))
  change max ‖(1 : ℝ) - 1‖
    (max ‖(configuration.movingStateVectorField first).2.1 - (configuration.movingStateVectorField second).2.1‖
      ‖(configuration.movingStateVectorField first).2.2 - (configuration.movingStateVectorField second).2.2‖) ≤ _
  apply max_le
  · simpa only [sub_self, norm_zero] using finalNonnegative
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg finalNonnegative).mpr
      intro index
      have actual := (configuration.movingStateVectorField_component_parameter_bounds positive centerNonnegative shapeNonnegative shapeSmall
        constantNonnegative derivativeBound derivativeDifference firstInside secondInside index).1
      exact actual.trans (mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_right (shapeTermNonnegative index)).trans (eachLe index)) (norm_nonneg (first - second)))
    · apply (pi_norm_le_iff_of_nonneg finalNonnegative).mpr
      intro index
      have actual := (configuration.movingStateVectorField_component_parameter_bounds positive centerNonnegative shapeNonnegative shapeSmall
        constantNonnegative derivativeBound derivativeDifference firstInside secondInside index).2
      exact actual.trans (mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_left (centerTermNonnegative index)).trans (eachLe index)) (norm_nonneg (first - second)))

end EulerNonuniqueness.Paper
