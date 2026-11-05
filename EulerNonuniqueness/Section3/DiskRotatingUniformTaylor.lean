import EulerNonuniqueness.Section3.DiskRotatingLocalSecondRegularity
import EulerNonuniqueness.General.LocalUniformQuadraticRemainder
import EulerNonuniqueness.General.LocalFiberOperatorBounds

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] rotatingSecondFrechetC1Group secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

theorem diskEulerRotatingField_exists_uniform_firstJet_bounds :
    ∃ radius > 0, radius ≤ 1 ∧ ∃ constant ≥ 1, ∀ data direction : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      ‖fderiv ℝ diskEulerRotatingField data‖ ≤ constant ∧
      ‖fderiv ℝ (fderiv ℝ diskEulerRotatingField) data‖ ≤ constant ∧
      ‖diskEulerRotatingField (data + direction) - diskEulerRotatingField data -
        fderiv ℝ diskEulerRotatingField data direction‖ ≤ constant * ‖direction‖ ^ 2 ∧
      ‖fderiv ℝ diskEulerRotatingField (data + direction) - fderiv ℝ diskEulerRotatingField data -
        fderiv ℝ (fderiv ℝ diskEulerRotatingField) data direction‖ ≤ constant * ‖direction‖ ^ 2 := by
  let shifted := fun increment : PeriodicC1HolderHalf => diskEulerRotatingField (standardCircleBanach + increment)
  let shiftedDerivative := fun increment : PeriodicC1HolderHalf => fderiv ℝ diskEulerRotatingField (standardCircleBanach + increment)
  have translation : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment) 0 :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (analyticAt_const.add analyticAt_id)
  have second := diskEulerRotatingField_derivative_hasLipschitzDerivativeNear
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have first : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskEulerRotatingField standardCircleBanach := by
    refine ⟨?_, second.lipschitzNear⟩
    filter_upwards [ball_mem_nhds standardCircleBanach threshold] with data member
    exact differentiableAt_diskEulerRotatingField data
      (by simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using member)
  have firstAt : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskEulerRotatingField (standardCircleBanach + 0) := by simpa using first
  have secondAt : EulerNonuniqueness.General.HasLipschitzDerivativeNear (fderiv ℝ diskEulerRotatingField) (standardCircleBanach + 0) := by simpa using second
  have shiftedFirst : EulerNonuniqueness.General.HasLipschitzDerivativeNear shifted 0 :=
    EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp (inner := fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment)
      firstAt translation
  have shiftedSecond : EulerNonuniqueness.General.HasLipschitzDerivativeNear shiftedDerivative 0 :=
    EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp (inner := fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment)
      secondAt translation
  obtain ⟨firstRadius, firstPositive, firstConstant, firstNonnegative, firstRemainder⟩ := shiftedFirst.exists_uniform_quadratic_remainder shifted
  obtain ⟨secondRadius, secondPositive, secondConstant, secondNonnegative, secondRemainder⟩ := shiftedSecond.exists_uniform_quadratic_remainder shiftedDerivative
  obtain ⟨firstBound, firstBoundNonnegative, firstBounded⟩ :=
    EulerNonuniqueness.General.exists_eventually_norm_bound (function := fderiv ℝ shifted) shiftedFirst.2.continuousAt
  obtain ⟨secondBound, secondBoundNonnegative, secondBounded⟩ :=
    EulerNonuniqueness.General.exists_eventually_norm_bound (function := fderiv ℝ shiftedDerivative) shiftedSecond.2.continuousAt
  obtain ⟨boundRadius, boundPositive, boundContained⟩ := Metric.mem_nhds_iff.mp (firstBounded.and secondBounded)
  let radius := min firstRadius (min secondRadius (min (boundRadius / 2) (min (1 / 2) (min 1 (2 / (3 * Real.pi)) / 2))))
  let constant := 1 + firstBound + secondBound + firstConstant + secondConstant
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have radiusFirst : radius ≤ firstRadius := min_le_left _ _
  have radiusSecond : radius ≤ secondRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusBound : radius ≤ boundRadius / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusOne : radius ≤ 1 / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have radiusThreshold : radius ≤ min 1 (2 / (3 * Real.pi)) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨radius, radiusPositive, by linarith, constant, by dsimp [constant]; linarith, ?_⟩
  intro data direction inside
  let base := data - standardCircleBanach
  have baseSmall : ‖base‖ ≤ radius := by change ‖data - standardCircleBanach‖ ≤ radius; linarith [norm_nonneg direction]
  have nearby : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have actual := baseSmall.trans radiusThreshold
    change ‖data - standardCircleBanach‖ ≤ _ at actual
    linarith
  have center : standardCircleBanach + base = data := by dsimp [base]; abel
  have translationDerivative : HasFDerivAt (fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment)
      (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) base := (hasFDerivAt_id base).const_add _
  have firstJet : fderiv ℝ shifted base = fderiv ℝ diskEulerRotatingField data := by
    have actual : HasFDerivAt diskEulerRotatingField (fderiv ℝ diskEulerRotatingField data) data :=
      DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (differentiableAt_diskEulerRotatingField data nearby)
    rw [← center] at actual
    have composed := HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (G := PeriodicC1HolderHalf) base actual translationDerivative
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, center] using composed.fderiv
  have secondJet : fderiv ℝ shiftedDerivative base = fderiv ℝ (fderiv ℝ diskEulerRotatingField) data := by
    have actual := diskEulerRotatingField_hasFDerivAt_fderiv data nearby
    rw [← center] at actual
    have composed := HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (G := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) base actual translationDerivative
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, center] using composed.fderiv
  have bounds := boundContained (show base ∈ ball 0 boundRadius by
    rw [mem_ball, dist_zero_right]
    have bound := baseSmall.trans radiusBound
    linarith)
  have firstError := firstRemainder base direction (inside.trans radiusFirst)
  have secondError := secondRemainder base direction (inside.trans radiusSecond)
  have shiftedEndpoint : standardCircleBanach + (base + direction) = data + direction := by rw [← add_assoc, center]
  dsimp only [shifted, shiftedDerivative] at firstError secondError
  rw [center, shiftedEndpoint, firstJet] at firstError
  rw [center, shiftedEndpoint, secondJet] at secondError
  change ‖fderiv ℝ shifted base‖ ≤ firstBound ∧ ‖fderiv ℝ shiftedDerivative base‖ ≤ secondBound at bounds
  rw [firstJet, secondJet] at bounds
  refine ⟨bounds.1.trans ?_, bounds.2.trans ?_, firstError.trans ?_, secondError.trans ?_⟩
  · dsimp [constant]; linarith
  · dsimp [constant]; linarith
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); dsimp [constant]; linarith
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); dsimp [constant]; linarith

end EulerNonuniqueness.Paper
