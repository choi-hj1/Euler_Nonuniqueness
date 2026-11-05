import EulerNonuniqueness.General.DistanceFieldCutoff
import EulerNonuniqueness.General.ODEClosedIntervalDerivative

noncomputable section

open Set Metric

namespace EulerNonuniqueness.General

theorem exists_jointly_continuous_cutoff_ODE_family
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    (field : Space → Space) (admissible : Set Space) {margin : ℝ} (positive : 0 < margin)
    (fieldConstant bound : NNReal)
    (fieldLipschitz : LipschitzOnWith fieldConstant field admissible)
    (fieldBound : ∀ point ∈ admissible, ‖field point‖ ≤ bound)
    {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon) :
    ∃ flow : Space → ℝ → Space,
      (∀ initial, flow initial 0 = initial) ∧
      Continuous (fun point : Space × ℝ => flow point.1 point.2) ∧
      (∀ initial time, time ∈ Icc 0 horizon →
        HasDerivWithinAt (flow initial)
          (distanceFieldCutoff admissible margin (flow initial time) • field (flow initial time))
          (Icc 0 horizon) time) ∧
      (∀ initial time, time ∈ Icc 0 horizon → margin ≤ infDist (flow initial time) admissibleᶜ →
        HasDerivWithinAt (flow initial) (field (flow initial time)) (Icc 0 horizon) time) ∧
      ∀ first second time, dist (flow first time) (flow second time) ≤ dist first second *
        Real.exp (((fieldConstant : ℝ) + margin⁻¹ * (bound : ℝ)) * horizon) := by
  obtain ⟨flow, initialIdentity, jointContinuous, derivatives, stability⟩ :=
    exists_jointly_continuous_family_of_bounded_lipschitz_ODE_with_closed_derivatives
      (lipschitzWith_distanceFieldCutoff_smul field admissible positive fieldConstant bound fieldLipschitz fieldBound)
      (distanceFieldCutoff_smul_norm_bound field admissible positive bound fieldBound) horizonNonnegative
  refine ⟨flow, initialIdentity, jointContinuous, derivatives, ?_, ?_⟩
  · intro initial time inside safe
    simpa only [distanceFieldCutoff_one admissible positive (flow initial time) safe, one_smul] using
      derivatives initial time inside
  · intro first second time
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk] using stability first second time

end EulerNonuniqueness.General
