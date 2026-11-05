import EulerNonuniqueness.Section3.DiskLinearGroup

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance neutralHistoryHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance neutralHistoryC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance neutralHistoryC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance neutralHistoryC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance neutralHistoryC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance neutralHistoryC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance neutralHistoryC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)

theorem diskLinearNeutral_hasDerivAt
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} (frequency time : ℝ)
    (radialEquation : HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial time) + radialForcing time) time)
    (angularEquation : HasDerivAt angular
      ((-frequency / 2) • radial time + angularForcing time) time) :
    HasDerivAt (fun current => angular current + periodicHilbertC1 (radial current))
      (angularForcing time + periodicHilbertC1 (radialForcing time) +
        (-frequency / 2) • periodicMeanProjectionCCLM (radial time)) time := by
  have linearDerivative : HasFDerivAt (fun data : PeriodicC1HolderHalf => periodicHilbertC1 data)
      periodicHilbertC1CLM (radial time) := by
    exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      periodicHilbertC1CLM
  have mapped : HasDerivAt (fun current => periodicHilbertC1 (radial current))
      (periodicHilbertC1 ((-frequency / 2) • periodicHilbertC1 (radial time) + radialForcing time)) time :=
    HasFDerivAt.comp_hasDerivAt (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) time linearDerivative radialEquation
  have neutral := HasDerivAt.add (F := PeriodicC1HolderHalf) angularEquation mapped
  convert neutral using 1
  rw [periodicHilbertC1_add, periodicHilbertC1_smul, periodicHilbertC1_sq]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change ((angularForcing time).val.1 label + (periodicHilbertC1 (radialForcing time)).val.1 label) +
      (-frequency / 2) • (periodicMeanProjectionCCLM (radial time)).val.1 label =
    ((-frequency / 2) • (radial time).val.1 label + (angularForcing time).val.1 label) +
      ((-frequency / 2) • (-((radial time).val.1 label -
        (periodicMeanProjectionCCLM (radial time)).val.1 label)) +
        (periodicHilbertC1 (radialForcing time)).val.1 label)
  simp only [Complex.real_smul]
  ring

theorem diskLinearNeutral_history
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ}
    (frequency : ℝ)
    (radialContinuous : ContinuousOn radial (Icc 0 horizon))
    (radialForcingContinuous : ContinuousOn radialForcing (Icc 0 horizon))
    (angularForcingContinuous : ContinuousOn angularForcing (Icc 0 horizon))
    (radialEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial current) + radialForcing current) current)
    (angularEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt angular
      ((-frequency / 2) • radial current + angularForcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    (angular time + periodicHilbertC1 (radial time)) - (angular 0 + periodicHilbertC1 (radial 0)) =
      ∫ current in (0 : ℝ)..time, angularForcing current + periodicHilbertC1 (radialForcing current) +
        (-frequency / 2) • periodicMeanProjectionCCLM (radial current) := by
  have sourceContinuous : ContinuousOn
      (fun current => angularForcing current + periodicHilbertC1 (radialForcing current) +
        (-frequency / 2) • periodicMeanProjectionCCLM (radial current)) (Icc 0 horizon) := by
    apply (angularForcingContinuous.add
      (periodicHilbertC1CLM.continuous.comp_continuousOn radialForcingContinuous)).add
    exact ((periodicMeanProjectionCCLM.restrictScalars ℝ).continuous.comp_continuousOn radialContinuous).const_smul _
  have subset : Icc 0 time ⊆ Icc 0 horizon := fun _ membership => ⟨membership.1, membership.2.trans inside.2⟩
  have sourceIntegrable : IntervalIntegrable
      (fun current => angularForcing current + periodicHilbertC1 (radialForcing current) +
        (-frequency / 2) • periodicMeanProjectionCCLM (radial current)) volume 0 time :=
    (sourceContinuous.mono subset).intervalIntegrable_of_Icc (E := PeriodicC1HolderHalf) inside.1
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (E := PeriodicC1HolderHalf)
    (fun current membership => diskLinearNeutral_hasDerivAt frequency current
      (radialEquation current (subset (by simpa only [uIcc_of_le inside.1] using membership)))
      (angularEquation current (subset (by simpa only [uIcc_of_le inside.1] using membership))))
    sourceIntegrable).symm

end

end EulerNonuniqueness.Paper
