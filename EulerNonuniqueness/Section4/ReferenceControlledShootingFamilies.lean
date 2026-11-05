import EulerNonuniqueness.Section4.ReferenceControlledCutoffFamily
import EulerNonuniqueness.Section4.ReferenceMechanicalInitialMonitors

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_controlled_reference_shooting_families :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
    ∀ count : ℕ, 0 < count → ∀ scales : Scales,
    0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
    ∀ (phase : Fin count → ℝ) (radius : ℝ), 0 < radius → radius ≤ 1 / 2 →
    ∃ configuration : FiniteContourConfiguration (count * 4),
      (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) ∧
      (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) ∧
    ∃ gap > (0 : ℝ), ∃ margin > (0 : ℝ),
      margin ≤ shapeRadius / 8 ∧ margin ≤ 1 / 8 ∧
      (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second) ∧
    ∃ trajectories : (parameter : closedBall (0 : Fin count → ℝ) radius) →
      MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3
        (referenceMechanicalInitialState scales phase parameter.val),
      (∀ parameter : closedBall (0 : Fin count → ℝ) radius,
        ReferenceInitialDisks scales (trajectories parameter).movingFamily.patchMotion phase parameter.val (1 / 2)) ∧
      (∀ parameter : closedBall (0 : Fin count → ℝ) radius,
        2 * margin ≤ infDist (referenceMechanicalInitialState scales phase parameter.val)
        (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ) ∧
      Continuous (fun point : closedBall (0 : Fin count → ℝ) radius × ℝ => (trajectories point.1).curve point.2) ∧
      (∀ parameter current, current ∈ Icc (0 : ℝ) 2 → ∀ label,
        ((trajectories parameter).curve current).2.2 label ∈ contourContinuousVectorSubmodule) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ := exists_uniform_controlled_reference_cutoff_families
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro count countPositive scales amplitudePositive frequencyPositive ratioPositive lengthSmall radiusSmall phase radius radiusPositive radiusBound
  obtain ⟨gap, gapPositive, margin, marginPositive, marginShape, marginUnit, marginSlack, trajectoriesExist⟩ :=
    families count countPositive scales amplitudePositive frequencyPositive ratioPositive lengthSmall radiusSmall
  let Parameter := closedBall (0 : Fin count → ℝ) radius
  letI : Nonempty Parameter := ⟨⟨0, by simpa only [Parameter, mem_closedBall, dist_self] using radiusPositive.le⟩⟩
  have unstableSmall (parameter : Parameter) (index : Fin count) : |parameter.val index| ≤ 1 / 2 := by
    have total : ‖parameter.val‖ ≤ radius := by simpa only [Parameter, mem_closedBall, dist_zero_right] using parameter.property
    exact ((show |parameter.val index| ≤ ‖parameter.val‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm parameter.val index).trans total).trans radiusBound
  obtain ⟨configuration, densityIdentity, radiusIdentity, trajectories, jointContinuous, initialMargin,
    shapeMember, _, initialDisks⟩ := trajectoriesExist phase (fun parameter : Parameter => parameter.val)
      continuous_subtype_val unstableSmall 1 (by norm_num) 3 (by norm_num)
  refine ⟨configuration, densityIdentity, radiusIdentity, gap, gapPositive, margin, marginPositive,
    marginShape, marginUnit, marginSlack, trajectories, initialDisks, initialMargin, jointContinuous, ?_⟩
  intro parameter current member label
  exact shapeMember parameter current ⟨member.1, by linarith [member.2]⟩ label

end EulerNonuniqueness.Paper
