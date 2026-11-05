import EulerNonuniqueness.General.TwoSidedODEFamily
import EulerNonuniqueness.General.SupportedODEInvariance

noncomputable section

open Set

namespace EulerNonuniqueness.General

theorem two_sided_trajectory_mem_of_lipschitz_field_zero_outside
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [CompleteSpace space]
    {field : space → space} {constant : NNReal} (lipschitz : LipschitzWith constant field)
    (admissible : Set space) (zeroOutside : ∀ state ∉ admissible, field state = 0)
    {trajectory : ℝ → space} {backwardHorizon forwardHorizon : ℝ}
    (backwardPositive : 0 < backwardHorizon) (forwardPositive : 0 < forwardHorizon)
    (continuous : Continuous trajectory)
    (equation : ∀ time ∈ Ioo (-backwardHorizon) forwardHorizon,
      HasDerivAt trajectory (field (trajectory time)) time)
    (initialInside : trajectory 0 ∈ admissible)
    (clamping : ∀ time, ∃ clampedTime ∈ Icc (-backwardHorizon) forwardHorizon,
      trajectory time = trajectory clampedTime) :
    ∀ time, trajectory time ∈ admissible := by
  have forwardEquation : ∀ time ∈ Icc 0 forwardHorizon,
      HasDerivWithinAt trajectory (field (trajectory time)) (Icc 0 forwardHorizon) time :=
    hasDerivWithinAt_Icc_of_continuous_interior_derivative continuous.continuousOn
      (lipschitz.continuous.comp continuous)
      (fun time inside => equation time ⟨by linarith [inside.1], inside.2⟩)
  have forwardInside := trajectory_mem_of_lipschitz_field_zero_outside lipschitz admissible
    zeroOutside continuous.continuousOn forwardEquation initialInside
  let reversed := fun time : ℝ => trajectory (-time)
  have reversedContinuous : Continuous reversed := continuous.comp continuous_neg
  have reversedInterior : ∀ time ∈ Ioo 0 backwardHorizon,
      HasDerivAt reversed ((-field) (reversed time)) time := by
    intro time inside
    have derivative := equation (-time) ⟨by linarith [inside.2], by linarith [inside.1]⟩
    simpa [reversed, Function.comp_def] using derivative.scomp time (hasDerivAt_id time).neg
  have reversedEquation := hasDerivWithinAt_Icc_of_continuous_interior_derivative
    reversedContinuous.continuousOn (lipschitz.neg.continuous.comp reversedContinuous) reversedInterior
  have backwardInside := trajectory_mem_of_lipschitz_field_zero_outside lipschitz.neg admissible
    (fun state outside => by simpa using congrArg Neg.neg (zeroOutside state outside))
    reversedContinuous.continuousOn reversedEquation (by simpa [reversed] using initialInside)
  intro time
  obtain ⟨clampedTime, inside, identity⟩ := clamping time
  rw [identity]
  by_cases nonnegative : 0 ≤ clampedTime
  · exact forwardInside clampedTime ⟨nonnegative, inside.2⟩
  · have member := backwardInside (-clampedTime) ⟨by linarith, by linarith [inside.1]⟩
    simpa [reversed] using member

end EulerNonuniqueness.General
