import EulerNonuniqueness.Section3.DiskRotatingRelativeTaylor

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

local instance rotatingPhysicalRelativeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskRotatingTaylorRemainder (base direction : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskEulerRotatingField (base + direction) - diskEulerRotatingField base -
    fderiv ℝ diskEulerRotatingField base direction

def diskRotatingDerivativeTaylorRemainder (base direction : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  fderiv ℝ diskEulerRotatingField (base + direction) - fderiv ℝ diskEulerRotatingField base -
    fderiv ℝ (fderiv ℝ diskEulerRotatingField) base direction

theorem diskRotatingOffset_fderiv (point : PeriodicC1HolderHalf) :
    fderiv ℝ diskRotatingOffset point = fderiv ℝ diskEulerRotatingField (standardCircleBanach + point) := by
  unfold diskRotatingOffset
  with_reducible_and_instances
    exact fderiv_comp_add_left (𝕜 := ℝ) (f := diskEulerRotatingField) standardCircleBanach

theorem diskRotatingDerivativeOffset_fderiv (point : PeriodicC1HolderHalf) :
    fderiv ℝ diskRotatingDerivativeOffset point =
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) (standardCircleBanach + point) := by
  unfold diskRotatingDerivativeOffset
  with_reducible_and_instances
    exact fderiv_comp_add_left (𝕜 := ℝ) (f := fderiv ℝ diskEulerRotatingField) standardCircleBanach

theorem diskRotatingTaylorRemainder_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖diskRotatingTaylorRemainder initialBase initialIncrement -
        diskRotatingTaylorRemainder finalBase finalIncrement‖ ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨radius, positive, constant, bound⟩ := diskRotatingOffset_exists_relative_quadratic_taylor_ball
  refine ⟨radius, positive, constant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside
  have actual := bound (initialBase - standardCircleBanach) (finalBase - standardCircleBanach)
    initialIncrement finalIncrement initialInside finalInside
  have shift (base direction : PeriodicC1HolderHalf) :
      standardCircleBanach + ((base - standardCircleBanach) + direction) = base + direction := by abel
  have center (base : PeriodicC1HolderHalf) : standardCircleBanach + (base - standardCircleBanach) = base := by abel
  have difference : (initialBase - standardCircleBanach) - (finalBase - standardCircleBanach) =
      initialBase - finalBase := by abel
  simpa only [diskRotatingOffset_fderiv, diskRotatingOffset, shift, center, difference,
    diskRotatingTaylorRemainder] using actual

theorem diskRotatingDerivativeTaylorRemainder_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖diskRotatingDerivativeTaylorRemainder initialBase initialIncrement -
        diskRotatingDerivativeTaylorRemainder finalBase finalIncrement‖ ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨radius, positive, constant, bound⟩ := diskRotatingDerivativeOffset_exists_relative_quadratic_taylor_ball
  refine ⟨radius, positive, constant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside
  have actual := bound (initialBase - standardCircleBanach) (finalBase - standardCircleBanach)
    initialIncrement finalIncrement initialInside finalInside
  have shift (base direction : PeriodicC1HolderHalf) :
      standardCircleBanach + ((base - standardCircleBanach) + direction) = base + direction := by abel
  have center (base : PeriodicC1HolderHalf) : standardCircleBanach + (base - standardCircleBanach) = base := by abel
  have difference : (initialBase - standardCircleBanach) - (finalBase - standardCircleBanach) =
      initialBase - finalBase := by abel
  simpa only [diskRotatingDerivativeOffset_fderiv, diskRotatingDerivativeOffset, shift, center, difference,
    diskRotatingDerivativeTaylorRemainder] using actual

end EulerNonuniqueness.Paper
