import EulerNonuniqueness.Section3.DiskRotatingRelativeTaylor
import EulerNonuniqueness.General.RelativeLinearIncrement

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

local instance rotatingIncrementC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskEulerRotatingField_derivative_exists_relative_increment_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖(fderiv ℝ diskEulerRotatingField (initialBase + initialIncrement) -
          fderiv ℝ diskEulerRotatingField initialBase) -
        (fderiv ℝ diskEulerRotatingField (finalBase + finalIncrement) -
          fderiv ℝ diskEulerRotatingField finalBase)‖ ≤ constant *
        (‖initialIncrement - finalIncrement‖ + ‖initialBase - finalBase‖ * ‖finalIncrement‖) := by
  have regular := diskRotatingDerivativeOffset_hasLipschitzSecondDerivativeNear.1
  obtain ⟨radius, positive, constant, nonnegative, bound⟩ :=
    EulerNonuniqueness.General.exists_relative_linear_increment_ball diskRotatingDerivativeOffset regular
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside
  have actual := bound (initialBase - standardCircleBanach) (finalBase - standardCircleBanach)
    initialIncrement finalIncrement initialInside finalInside
  have shift (base direction : PeriodicC1HolderHalf) :
      standardCircleBanach + ((base - standardCircleBanach) + direction) = base + direction := by abel
  have center (base : PeriodicC1HolderHalf) : standardCircleBanach + (base - standardCircleBanach) = base := by abel
  have difference : (initialBase - standardCircleBanach) - (finalBase - standardCircleBanach) =
      initialBase - finalBase := by abel
  simpa only [diskRotatingDerivativeOffset, shift, center, difference] using actual

end EulerNonuniqueness.Paper
