import EulerNonuniqueness.Section3.DiskForcedGroup
import EulerNonuniqueness.Section3.DiskNeutralHistory

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance forcedResponseHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance forcedResponseC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance forcedResponseC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance forcedResponseC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance forcedResponseC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance forcedResponseC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance forcedResponseC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)

def diskEffectiveForcing (frequency : ℝ) (radial radialForcing angularForcing : PeriodicC1HolderHalf) :
    DiskLinearState :=
  (radialForcing, angularForcing + (-frequency / 2) • periodicMeanProjectionCCLM radial)

theorem diskEffectiveForcing_norm_le (frequency : ℝ)
    (radial radialForcing angularForcing : PeriodicC1HolderHalf) :
    ‖diskEffectiveForcing frequency radial radialForcing angularForcing‖ ≤
      ‖radialForcing‖ + ‖angularForcing‖ + |frequency| / 2 * ‖periodicMeanProjectionCCLM radial‖ := by
  have coefficient : ‖(-frequency / 2 : ℝ)‖ = |frequency| / 2 := by
    rw [Real.norm_eq_abs, abs_div, abs_neg]
    norm_num
  have meanBound : ‖(-frequency / 2) • periodicMeanProjectionCCLM radial‖ ≤
      |frequency| / 2 * ‖periodicMeanProjectionCCLM radial‖ := by
    calc
      _ ≤ ‖(-frequency / 2 : ℝ)‖ * ‖periodicMeanProjectionCCLM radial‖ := norm_smul_le _ _
      _ = _ := by rw [coefficient]
  change max ‖radialForcing‖ ‖angularForcing + (-frequency / 2) • periodicMeanProjectionCCLM radial‖ ≤ _
  apply max_le
  · have meanNonnegative : 0 ≤ |frequency| / 2 * ‖periodicMeanProjectionCCLM radial‖ := by positivity
    linarith [norm_nonneg angularForcing]
  · calc
      _ ≤ ‖angularForcing‖ + ‖(-frequency / 2) • periodicMeanProjectionCCLM radial‖ :=
        norm_add_le angularForcing ((-frequency / 2) • periodicMeanProjectionCCLM radial)
      _ ≤ _ := by linarith [norm_nonneg radialForcing]

theorem diskRawPair_hasDerivAt
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} (frequency time : ℝ)
    (radialEquation : HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial time) + radialForcing time) time)
    (angularEquation : HasDerivAt angular
      ((-frequency / 2) • radial time + angularForcing time) time) :
    HasDerivAt (fun current => (radial current, angular current))
      ((frequency • diskLinearGenerator) (radial time, angular time) +
        diskEffectiveForcing frequency (radial time) (radialForcing time) (angularForcing time)) time := by
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
  · change frequency • ((-1 / 2 : ℝ) • ((radial time).val.1 label -
        (periodicMeanProjectionCCLM (radial time)).val.1 label)) +
        ((angularForcing time).val.1 label + (-frequency / 2) •
          (periodicMeanProjectionCCLM (radial time)).val.1 label) =
      (-frequency / 2) • (radial time).val.1 label + (angularForcing time).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring

theorem diskEffectiveForcing_continuousOn
    {radial radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {domain : Set ℝ} (frequency : ℝ)
    (radialContinuous : ContinuousOn radial domain)
    (radialForcingContinuous : ContinuousOn radialForcing domain)
    (angularForcingContinuous : ContinuousOn angularForcing domain) :
    ContinuousOn (fun time => diskEffectiveForcing frequency (radial time)
      (radialForcing time) (angularForcing time)) domain := by
  exact radialForcingContinuous.prodMk (angularForcingContinuous.add
    (((periodicMeanProjectionCCLM.restrictScalars ℝ).continuous.comp_continuousOn radialContinuous).const_smul _))

theorem diskRawPair_response_bound
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ}
    (frequency : ℝ)
    (radialContinuous : ContinuousOn radial (Icc 0 horizon))
    (angularContinuous : ContinuousOn angular (Icc 0 horizon))
    (radialForcingContinuous : ContinuousOn radialForcing (Icc 0 horizon))
    (angularForcingContinuous : ContinuousOn angularForcing (Icc 0 horizon))
    (radialEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial current) + radialForcing current) current)
    (angularEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt angular
      ((-frequency / 2) • radial current + angularForcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    ‖(radial time, angular time)‖ ≤ diskLinearGroupBound *
      (‖(radial 0, angular 0)‖ + ∫ current in (0 : ℝ)..time,
        ‖diskEffectiveForcing frequency (radial current) (radialForcing current) (angularForcing current)‖) := by
  with_reducible
    exact diskLinearRateGroup_response_bound
      (trajectory := fun current => (radial current, angular current))
      (forcing := fun current => diskEffectiveForcing frequency (radial current)
        (radialForcing current) (angularForcing current)) (horizon := horizon) (time := time) frequency
      (radialContinuous.prodMk angularContinuous)
      (diskEffectiveForcing_continuousOn frequency radialContinuous radialForcingContinuous angularForcingContinuous)
      (fun current membership => diskRawPair_hasDerivAt frequency current
        (radialEquation current membership) (angularEquation current membership)) inside

theorem diskRawPair_duhamel
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ}
    (frequency : ℝ)
    (radialContinuous : ContinuousOn radial (Icc 0 horizon))
    (angularContinuous : ContinuousOn angular (Icc 0 horizon))
    (radialForcingContinuous : ContinuousOn radialForcing (Icc 0 horizon))
    (angularForcingContinuous : ContinuousOn angularForcing (Icc 0 horizon))
    (radialEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial current) + radialForcing current) current)
    (angularEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt angular
      ((-frequency / 2) • radial current + angularForcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    (radial time, angular time) = diskLinearRateGroup frequency time (radial 0, angular 0) +
      ∫ current in (0 : ℝ)..time, diskLinearRateGroup frequency (time - current)
        (diskEffectiveForcing frequency (radial current) (radialForcing current) (angularForcing current)) := by
  exact diskLinearRateGroup_duhamel frequency
    (radialContinuous.prodMk angularContinuous)
    (diskEffectiveForcing_continuousOn frequency radialContinuous radialForcingContinuous angularForcingContinuous)
    (fun current membership => diskRawPair_hasDerivAt frequency current
      (radialEquation current membership) (angularEquation current membership)) inside

theorem diskRawPair_response_bound_explicit
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ}
    (frequency : ℝ)
    (radialContinuous : ContinuousOn radial (Icc 0 horizon))
    (angularContinuous : ContinuousOn angular (Icc 0 horizon))
    (radialForcingContinuous : ContinuousOn radialForcing (Icc 0 horizon))
    (angularForcingContinuous : ContinuousOn angularForcing (Icc 0 horizon))
    (radialEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial current) + radialForcing current) current)
    (angularEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt angular
      ((-frequency / 2) • radial current + angularForcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    ‖(radial time, angular time)‖ ≤ diskLinearGroupBound *
      (‖(radial 0, angular 0)‖ + ∫ current in (0 : ℝ)..time,
        ‖radialForcing current‖ + ‖angularForcing current‖ +
          |frequency| / 2 * ‖periodicMeanProjectionCCLM (radial current)‖) := by
  have subset : Icc 0 time ⊆ Icc 0 horizon := fun _ membership => ⟨membership.1, membership.2.trans inside.2⟩
  have effectiveContinuous := diskEffectiveForcing_continuousOn frequency
    radialContinuous radialForcingContinuous angularForcingContinuous
  have majorantContinuous : ContinuousOn (fun current =>
      ‖radialForcing current‖ + ‖angularForcing current‖ +
        |frequency| / 2 * ‖periodicMeanProjectionCCLM (radial current)‖) (Icc 0 horizon) :=
    (radialForcingContinuous.norm.add angularForcingContinuous.norm).add
      (continuous_const.continuousOn.mul
        (ContinuousOn.norm (E := PeriodicC1HolderHalf)
          ((periodicMeanProjectionCCLM.restrictScalars ℝ).continuous.comp_continuousOn radialContinuous)))
  apply (diskRawPair_response_bound frequency radialContinuous angularContinuous
    radialForcingContinuous angularForcingContinuous radialEquation angularEquation inside).trans
  apply mul_le_mul_of_nonneg_left _ diskLinearGroupBound_nonnegative
  apply add_le_add_left
  exact intervalIntegral.integral_mono_on inside.1
    ((ContinuousOn.norm (E := DiskLinearState) (effectiveContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1)
    ((majorantContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1)
    (fun current _ => diskEffectiveForcing_norm_le frequency _ _ _)

theorem diskRawPair_response_bound_of_mean_zero
    {radial angular radialForcing angularForcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ}
    (frequency : ℝ)
    (radialContinuous : ContinuousOn radial (Icc 0 horizon))
    (angularContinuous : ContinuousOn angular (Icc 0 horizon))
    (radialForcingContinuous : ContinuousOn radialForcing (Icc 0 horizon))
    (angularForcingContinuous : ContinuousOn angularForcing (Icc 0 horizon))
    (radialEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt radial
      ((-frequency / 2) • periodicHilbertC1 (radial current) + radialForcing current) current)
    (angularEquation : ∀ current ∈ Icc 0 horizon, HasDerivAt angular
      ((-frequency / 2) • radial current + angularForcing current) current)
    (meanZero : ∀ current ∈ Icc 0 horizon, c1AngularIntegralCCLM (radial current) = 0)
    (inside : time ∈ Icc 0 horizon) :
    ‖(radial time, angular time)‖ ≤ diskLinearGroupBound *
      (‖(radial 0, angular 0)‖ + ∫ current in (0 : ℝ)..time,
        ‖radialForcing current‖ + ‖angularForcing current‖) := by
  have actual := diskRawPair_response_bound_explicit frequency radialContinuous angularContinuous
    radialForcingContinuous angularForcingContinuous radialEquation angularEquation inside
  convert actual using 1
  congr 2
  apply intervalIntegral.integral_congr
  intro current membership
  have currentInside : current ∈ Icc 0 horizon := by
    have intervalInside : current ∈ Icc 0 time := by simpa only [uIcc_of_le inside.1] using membership
    exact ⟨intervalInside.1, intervalInside.2.trans inside.2⟩
  have projectionZero : periodicMeanProjectionCCLM (radial current) = 0 := by
    exact periodicMeanProjectionCCLM_of_integral_zero _ (meanZero current currentInside)
  dsimp only
  rw [projectionZero, norm_zero (E := PeriodicC1HolderHalf), mul_zero, add_zero]

end

end EulerNonuniqueness.Paper
