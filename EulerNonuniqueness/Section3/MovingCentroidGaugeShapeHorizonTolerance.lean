import EulerNonuniqueness.Section3.MovingCentroidGaugeShapeHistory
import EulerNonuniqueness.General.QuarticConfinementBudget

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance movingGaugeShapeHorizonToleranceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem exists_uniform_spectral_shape_confinement_with_tolerance_on_horizon :
    ∃ radius > 0, ∀ forcingConstant horizon shapeTolerance : ℝ,
      0 ≤ forcingConstant → 0 ≤ horizon → 0 < shapeTolerance →
      ∃ rootMin ≥ (8 : ℝ),
      ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
      ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ horizon →
      ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
        {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
        {initial : MovingContourState count}
        (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
          backwardHorizon forwardHorizon initial),
      (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
      terminal < forwardHorizon →
      (∀ current ∈ Icc 0 terminal, margin ≤ infDist (trajectory.curve current)
        (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
      ∀ (index : Fin count) (frequency distance weight : ℝ),
      1 ≤ frequency → |configuration.density index| = scaleRoot ^ 3 * frequency ^ 4 →
      0 < distance → 0 ≤ weight → weight ≤ forcingConstant * frequency →
      192 * (trajectory.movingFamily.patch index).radius ≤ distance →
      (∀ current ∈ Icc 0 terminal, ∀ source ∈ Finset.univ.erase index,
        ∀ position ∈ (trajectory.movingFamily.patch source).domain current,
        distance ≤ ‖(trajectory.movingFamily.patch index).center current - position‖) →
      (∀ current ∈ Icc 0 terminal, (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) current)
        ((trajectory.movingFamily.patch index).center current) position) ≤ weight) →
      (∀ current ∈ Icc 0 terminal, ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < radius) →
      (∀ current ∈ Icc 0 terminal,
        ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index current)‖ ≤
          (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) →
      ∀ time ∈ Icc 0 terminal,
        ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < shapeTolerance := by
  obtain ⟨radius, positiveRadius, neutralConstant, neutralOne, shapeConstant, shapeOne, histories⟩ :=
    exists_uniform_spectral_shape_history_radius
  refine ⟨radius, positiveRadius, ?_⟩
  intro forcingConstant horizon shapeTolerance forcingNonnegative horizonNonnegative tolerancePositive
  obtain ⟨rootMin, rootEight, budgets⟩ :=
    EulerNonuniqueness.General.exists_uniform_quartic_shape_confinement_root
      forcingNonnegative (show 0 ≤ neutralConstant by linarith) (show 0 ≤ shapeConstant by linarith)
      horizonNonnegative tolerancePositive
  refine ⟨rootMin, rootEight, ?_⟩
  intro scaleRoot rootLarge terminal terminalNonnegative terminalBound count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon
    initial trajectory initialCircles initialClock marginPositive beforeFinal safe index frequency distance weight
    frequencyLarge densityIdentity distancePositive weightNonnegative weightBound small separated weightBounds nearby
    transverseBounds time inside
  have scalar := budgets scaleRoot rootLarge frequency weight frequencyLarge weightNonnegative weightBound
  dsimp only at scalar
  have history := histories trajectory initialCircles initialClock marginPositive
    terminal distance weight ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) beforeFinal safe
    index distancePositive weightNonnegative scalar.1.le small separated weightBounds nearby transverseBounds time inside
  rw [densityIdentity] at history
  have rateNonnegative : 0 ≤ neutralConstant *
      ((scaleRoot ^ 3 * frequency ^ 4) * ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) ^ 2 +
        weight * ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2))) := by
    have rootPositive : 0 < scaleRoot := by linarith [rootEight.trans rootLarge]
    have frequencyPositive : 0 < frequency := by linarith
    positivity
  have atTerminal := mul_le_mul_of_nonneg_left (inside.2.trans terminalBound) rateNonnegative
  exact history.trans_lt ((mul_le_mul_of_nonneg_left (add_le_add_right atTerminal _)
    (show 0 ≤ shapeConstant by linarith)).trans_lt scalar.2.2.2)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

