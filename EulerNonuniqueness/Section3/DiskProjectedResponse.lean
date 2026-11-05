import EulerNonuniqueness.Section3.DiskForcedResponse

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance projectedResponseHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance projectedResponseC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance projectedResponseC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance projectedResponseC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance projectedResponseC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance projectedResponseC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance projectedResponseC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)

theorem diskProjectedPair_hasDerivAt
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} (frequency time : ℝ)
    (radialEquation : HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial time) + radialForcing time) time)
    (angularEquation : HasDerivAt angular
      ((-frequency / 2) • periodicMeanZeroPartCCLM (radial time) + angularForcing time) time) :
    HasDerivAt (fun current => (radial current, angular current))
      ((frequency • diskLinearGenerator) (radial time, angular time) +
        (radialForcing time, angularForcing time)) time := by
  have actual := HasDerivAt.prodMk (F := PeriodicC1HolderHalf) (G := PeriodicC1HolderHalf)
    radialEquation angularEquation
  convert actual using 1
  rw [ContinuousLinearMap.smul_apply, diskLinearGenerator_apply]
  apply Prod.ext <;> apply PeriodicC1HolderHalf.ext_value <;> intro label
  · change frequency • ((-1 / 2 : ℝ) • (periodicHilbertC1 (radial time)).val.1 label) +
        (radialForcing time).val.1 label =
      (-frequency / 2) • (periodicHilbertC1 (radial time)).val.1 label + (radialForcing time).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring
  · change frequency • ((-1 / 2 : ℝ) • (periodicMeanZeroPartCCLM (radial time)).val.1 label) +
        (angularForcing time).val.1 label =
      (-frequency / 2) • (periodicMeanZeroPartCCLM (radial time)).val.1 label + (angularForcing time).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring

theorem diskProjectedPair_response_bound
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ}
    (frequency : ℝ)
    (radialContinuous : ContinuousOn radial (Icc 0 horizon))
    (angularContinuous : ContinuousOn angular (Icc 0 horizon))
    (radialForcingContinuous : ContinuousOn radialForcing (Icc 0 horizon))
    (angularForcingContinuous : ContinuousOn angularForcing (Icc 0 horizon))
    (radialEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial current) + radialForcing current) current)
    (angularEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt angular
      ((-frequency / 2) • periodicMeanZeroPartCCLM (radial current) + angularForcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    ‖(radial time, angular time)‖ ≤ diskLinearGroupBound *
      (‖(radial 0, angular 0)‖ + ∫ current in (0 : ℝ)..time,
        ‖radialForcing current‖ + ‖angularForcing current‖) := by
  have subset : Icc 0 time ⊆ Icc 0 horizon := fun _ membership => ⟨membership.1, membership.2.trans inside.2⟩
  have actual : ‖(radial time, angular time)‖ ≤ diskLinearGroupBound *
      (‖(radial 0, angular 0)‖ + ∫ current in (0 : ℝ)..time,
        ‖(radialForcing current, angularForcing current)‖) := by
    with_reducible
      exact diskLinearRateGroup_response_bound
        (trajectory := fun current => (radial current, angular current))
        (forcing := fun current => (radialForcing current, angularForcing current))
        (horizon := horizon) (time := time) frequency
        (radialContinuous.prodMk angularContinuous) (radialForcingContinuous.prodMk angularForcingContinuous)
        (fun current membership => diskProjectedPair_hasDerivAt frequency current
          (radialEquation current membership) (angularEquation current membership)) inside
  apply actual.trans
  apply mul_le_mul_of_nonneg_left _ diskLinearGroupBound_nonnegative
  apply add_le_add_left
  exact intervalIntegral.integral_mono_on inside.1
    ((ContinuousOn.norm (E := DiskLinearState)
      ((radialForcingContinuous.prodMk angularForcingContinuous).mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1)
    (((radialForcingContinuous.norm.add angularForcingContinuous.norm).mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1)
    (fun current _ => max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _)))

theorem diskProjectedNeutral_hasDerivAt
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} (frequency time : ℝ)
    (radialEquation : HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial time) + radialForcing time) time)
    (angularEquation : HasDerivAt angular
      ((-frequency / 2) • periodicMeanZeroPartCCLM (radial time) + angularForcing time) time) :
    HasDerivAt (fun current => angular current + periodicHilbertC1 (radial current))
      (angularForcing time + periodicHilbertC1 (radialForcing time)) time := by
  have linearDerivative : HasFDerivAt (fun data : PeriodicC1HolderHalf => periodicHilbertC1 data)
      periodicHilbertC1CLM (radial time) := by
    exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) periodicHilbertC1CLM
  have mapped : HasDerivAt (fun current => periodicHilbertC1 (radial current))
      (periodicHilbertC1 ((-frequency / 2) • periodicHilbertC1 (radial time) + radialForcing time)) time :=
    HasFDerivAt.comp_hasDerivAt (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) time linearDerivative radialEquation
  have actual := HasDerivAt.add (F := PeriodicC1HolderHalf) angularEquation mapped
  convert actual using 1
  rw [periodicHilbertC1_add, periodicHilbertC1_smul, periodicHilbertC1_sq]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (angularForcing time).val.1 label + (periodicHilbertC1 (radialForcing time)).val.1 label =
    ((-frequency / 2) • (periodicMeanZeroPartCCLM (radial time)).val.1 label +
      (angularForcing time).val.1 label) +
      ((-frequency / 2) • (-(periodicMeanZeroPartCCLM (radial time)).val.1 label) +
        (periodicHilbertC1 (radialForcing time)).val.1 label)
  simp only [Complex.real_smul]
  ring

theorem diskProjectedNeutral_history
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ}
    (frequency : ℝ)
    (radialForcingContinuous : ContinuousOn radialForcing (Icc 0 horizon))
    (angularForcingContinuous : ContinuousOn angularForcing (Icc 0 horizon))
    (radialEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial current) + radialForcing current) current)
    (angularEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt angular
      ((-frequency / 2) • periodicMeanZeroPartCCLM (radial current) + angularForcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    (angular time + periodicHilbertC1 (radial time)) - (angular 0 + periodicHilbertC1 (radial 0)) =
      ∫ current in (0 : ℝ)..time, angularForcing current + periodicHilbertC1 (radialForcing current) := by
  have subset : Icc 0 time ⊆ Icc 0 horizon := fun _ membership => ⟨membership.1, membership.2.trans inside.2⟩
  have sourceContinuous : ContinuousOn
      (fun current => angularForcing current + periodicHilbertC1 (radialForcing current)) (Icc 0 horizon) :=
    angularForcingContinuous.add (periodicHilbertC1CLM.continuous.comp_continuousOn radialForcingContinuous)
  have sourceIntegrable : IntervalIntegrable
      (fun current => angularForcing current + periodicHilbertC1 (radialForcing current)) volume 0 time :=
    (sourceContinuous.mono subset).intervalIntegrable_of_Icc (E := PeriodicC1HolderHalf) inside.1
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (E := PeriodicC1HolderHalf)
    (fun current membership => diskProjectedNeutral_hasDerivAt frequency current
      (radialEquation current (subset (by simpa only [uIcc_of_le inside.1] using membership)))
      (angularEquation current (subset (by simpa only [uIcc_of_le inside.1] using membership))))
    sourceIntegrable).symm

end

end EulerNonuniqueness.Paper
