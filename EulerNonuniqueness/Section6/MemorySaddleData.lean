import EulerNonuniqueness.Section6.MemorySaddleConstants
import EulerNonuniqueness.Section6.IntegrableUnstableDuhamel

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

structure MemorySaddleSystem (parameters : MemorySaddleParameters) (horizon scale : ℝ) where
  trajectory : ℝ → ℝ
  forcing : ℝ → ℝ
  remainder : ℝ → ℝ
  stable : ℝ → ℝ
  history : ℝ → ℝ
  drive : ℝ → ℝ
  returned : ℝ → ℝ
  localCoefficient : ℝ → ℝ
  kernel : ℝ → ℝ → ℝ
  equation : ∀ time ∈ Icc 0 horizon, HasDerivAt trajectory
    (parameters.growth * trajectory time + scale * forcing time + remainder time) time
  forcingIntegrable : IntervalIntegrable (fun time => Real.exp (-parameters.growth * time) * forcing time) volume 0 horizon
  remainderMeasurable : AEStronglyMeasurable remainder (volume.restrict (Icc 0 horizon))
  stableContinuous : ContinuousOn stable (Icc 0 horizon)
  historyContinuous : ContinuousOn history (Icc 0 horizon)
  driveContinuous : ContinuousOn drive (Icc 0 horizon)
  returnedContinuous : ContinuousOn returned (Icc 0 horizon)
  stableNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ stable time
  historyNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ history time
  driveNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ drive time
  driveBound : ∀ time ∈ Icc 0 horizon,
    drive time ≤ scale * parameters.driveAmplitude * Real.exp (parameters.slowRate * time)
  localNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ localCoefficient time
  kernelContinuous : ∀ time ∈ Icc 0 horizon, ContinuousOn (kernel time) (Icc 0 time)
  kernelNonnegative : ∀ time ∈ Icc 0 horizon, ∀ current ∈ Icc 0 time, 0 ≤ kernel time current
  kernelBound : ∀ time ∈ Icc 0 horizon, localCoefficient time +
    (∫ current in (0 : ℝ)..time, kernel time current * Real.exp (parameters.growth * (current - time))) ≤ parameters.smallness
  returnedEquation : ∀ time ∈ Icc 0 horizon, returned time =
    localCoefficient time * (|trajectory time| + stable time + history time) +
      ∫ current in (0 : ℝ)..time, kernel time current * (|trajectory current| + stable current + history current)
  stableInequality : ∀ time ∈ Icc 0 horizon, stable time ≤ scale * parameters.stableInitial * Real.exp (parameters.rate * time) +
    parameters.multiplier * ∫ current in (0 : ℝ)..time, Real.exp (parameters.rate * (time - current)) *
      (parameters.smallness * |trajectory current| + parameters.chart * stable current + parameters.smallness * history current + returned current)
  historyInequality : ∀ time ∈ Icc 0 horizon, history time ≤ scale * parameters.historyInitial * Real.exp (parameters.rate * time) +
    parameters.multiplier * ∫ current in (0 : ℝ)..time, Real.exp (parameters.rate * (time - current)) *
      (|trajectory current| + stable current + drive current + parameters.smallness * history current + returned current)
  remainderBound : ∀ time ∈ Icc 0 horizon, |remainder time| ≤ parameters.multiplier *
    (parameters.smallness * (|trajectory time| + stable time) +
      (|trajectory time| + stable time) * (stable time + drive time) + parameters.smallness * history time) + returned time
  directInputBound : ∀ time ∈ Icc 0 horizon,
    |trajectory 0 + scale * (∫ current in (0 : ℝ)..time, Real.exp (-parameters.growth * current) * forcing current)| ≤
      scale * parameters.directAmplitude

namespace MemorySaddleSystem

theorem trajectoryContinuous {parameters : MemorySaddleParameters} {horizon scale : ℝ}
    (system : MemorySaddleSystem parameters horizon scale) : ContinuousOn system.trajectory (Icc 0 horizon) :=
  fun time inside => (system.equation time inside).continuousAt.continuousWithinAt

def restrict {parameters : MemorySaddleParameters} {horizon scale smaller : ℝ}
    (system : MemorySaddleSystem parameters horizon scale) (smallerInside : smaller ∈ Icc 0 horizon) :
    MemorySaddleSystem parameters smaller scale where
  trajectory := system.trajectory
  forcing := system.forcing
  remainder := system.remainder
  stable := system.stable
  history := system.history
  drive := system.drive
  returned := system.returned
  localCoefficient := system.localCoefficient
  kernel := system.kernel
  equation := fun time inside => system.equation time ⟨inside.1, inside.2.trans smallerInside.2⟩
  forcingIntegrable := system.forcingIntegrable.mono_set (by
    rw [uIcc_of_le smallerInside.1, uIcc_of_le (smallerInside.1.trans smallerInside.2)]
    exact Icc_subset_Icc le_rfl smallerInside.2)
  remainderMeasurable := system.remainderMeasurable.mono_measure
    (Measure.restrict_mono (Icc_subset_Icc le_rfl smallerInside.2) le_rfl)
  stableContinuous := system.stableContinuous.mono (Icc_subset_Icc le_rfl smallerInside.2)
  historyContinuous := system.historyContinuous.mono (Icc_subset_Icc le_rfl smallerInside.2)
  driveContinuous := system.driveContinuous.mono (Icc_subset_Icc le_rfl smallerInside.2)
  returnedContinuous := system.returnedContinuous.mono (Icc_subset_Icc le_rfl smallerInside.2)
  stableNonnegative := fun time inside => system.stableNonnegative time ⟨inside.1, inside.2.trans smallerInside.2⟩
  historyNonnegative := fun time inside => system.historyNonnegative time ⟨inside.1, inside.2.trans smallerInside.2⟩
  driveNonnegative := fun time inside => system.driveNonnegative time ⟨inside.1, inside.2.trans smallerInside.2⟩
  driveBound := fun time inside => system.driveBound time ⟨inside.1, inside.2.trans smallerInside.2⟩
  localNonnegative := fun time inside => system.localNonnegative time ⟨inside.1, inside.2.trans smallerInside.2⟩
  kernelContinuous := fun time inside => system.kernelContinuous time ⟨inside.1, inside.2.trans smallerInside.2⟩
  kernelNonnegative := fun time inside => system.kernelNonnegative time ⟨inside.1, inside.2.trans smallerInside.2⟩
  kernelBound := fun time inside => system.kernelBound time ⟨inside.1, inside.2.trans smallerInside.2⟩
  returnedEquation := fun time inside => system.returnedEquation time ⟨inside.1, inside.2.trans smallerInside.2⟩
  stableInequality := fun time inside => system.stableInequality time ⟨inside.1, inside.2.trans smallerInside.2⟩
  historyInequality := fun time inside => system.historyInequality time ⟨inside.1, inside.2.trans smallerInside.2⟩
  remainderBound := fun time inside => system.remainderBound time ⟨inside.1, inside.2.trans smallerInside.2⟩
  directInputBound := fun time inside => system.directInputBound time ⟨inside.1, inside.2.trans smallerInside.2⟩

end MemorySaddleSystem
end EulerNonuniqueness.Section6
