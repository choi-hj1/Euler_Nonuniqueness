import EulerNonuniqueness.Section6.SeparatingOrbitUniformGap
import EulerNonuniqueness.Section6.FourPointPassageStability

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem normalizedSeparatingOrbit_forced_passage_comparison
    (orbit : EulerNonuniqueness.Paper.SeparatingOrbit)
    (normalized : EulerNonuniqueness.Paper.IsNormalizedSeparatingOrbit orbit) :
    ∃ referenceGap > (0 : ℝ), ∀ {gap horizon forcing : ℝ}, 0 < gap → gap ≤ referenceGap →
    0 < horizon → 0 ≤ forcing → ∀ incomingTime : ℝ,
    ∀ actual error : ℝ → FourPointConfiguration,
    ContinuousOn actual (Icc 0 horizon) → ContinuousOn error (Icc 0 horizon) →
    (∀ time ∈ Ioo 0 horizon, HasDerivAt actual (fourPointField 1 (actual time) + error time) time) →
    (∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target → gap ≤ ‖actual time target - actual time source‖) →
    (∀ time ∈ Icc 0 horizon, ‖error time‖ ≤ forcing) →
    ∀ time ∈ Icc 0 horizon,
      ‖actual time - centrallySymmetricFourPoint (orbit.positive (time + incomingTime))
          (-orbit.negative (time + incomingTime))‖ ≤
        (‖actual 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (-orbit.negative incomingTime)‖ +
          forcing * time) * Real.exp ((8 / gap ^ 2) * time) := by
  obtain ⟨referenceGap, referencePositive, referenceSeparated⟩ :=
    normalizedSeparatingOrbit_uniform_pair_gap orbit normalized
  refine ⟨referenceGap, referencePositive, ?_⟩
  intro gap horizon forcing gapPositive gapSmall horizonPositive forcingNonnegative incomingTime
    actual error actualContinuous errorContinuous actualEquation actualSeparated errorBound
  let reference : ℝ → FourPointConfiguration := fun time =>
    centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (-orbit.negative (time + incomingTime))
  have referenceDerivative (time : ℝ) : HasDerivAt reference (fourPointField 1 (reference time)) time := by
    have actual := (normalizedSeparatingOrbit_full_point_equation orbit normalized (time + incomingTime)).1.scomp
      time ((hasDerivAt_id time).add_const incomingTime)
    simpa only [one_smul, Function.comp_def] using actual
  have referenceContinuous : ContinuousOn reference (Icc 0 horizon) :=
    fun time _ => (referenceDerivative time).continuousAt.continuousWithinAt
  have separated (time : ℝ) (_ : time ∈ Icc 0 horizon) (target source : Fin 4) (different : source ≠ target) :
      gap ≤ ‖reference time target - reference time source‖ :=
    gapSmall.trans (referenceSeparated (time + incomingTime) target source different.symm)
  have result := fourPoint_forced_passage_error horizonPositive gapPositive forcingNonnegative
    actualContinuous referenceContinuous errorContinuous actualEquation
    (fun time _ => referenceDerivative time) actualSeparated separated errorBound
  simpa only [reference, zero_add, abs_one, mul_one] using result

end EulerNonuniqueness.Section6
