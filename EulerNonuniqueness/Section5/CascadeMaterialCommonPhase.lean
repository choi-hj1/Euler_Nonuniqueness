import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair
import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialData

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

theorem CascadeMaterialPreparedPair.common_material_phase
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    {terminal time : ℝ} (terminalBound : terminal ≤ 1) (inside : time ∈ Icc 0 terminal)
    (safe : ∀ current ∈ Icc 0 terminal, prepared.margin ≤ infDist (prepared.trajectory.curve current)
      (prepared.configuration.movingStateAdmissible 4 shapeRadius prepared.gap)ᶜ)
    (index : Fin count) (patch : Fin 4) :
    (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).phase time =
      (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).phase time ∧
    (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).phase time =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2 := by
  have referencePhase := prepared.referenceWitness.trajectory.movingPatch_phase_eq_density_time_of_margin
    rfl prepared.referenceWitness.marginPositive
    (show time ∈ Icc (0 : ℝ) 2 from ⟨inside.1, by linarith [inside.2]⟩)
    prepared.referenceWitness.safe (finProdFinEquiv (index, patch))
  have alternativePhase := prepared.trajectory.movingPatch_phase_eq_density_time_of_margin rfl
    prepared.marginPositive inside safe (finProdFinEquiv (index, patch))
  rw [prepared.referenceWitness.densityIdentity] at referencePhase
  rw [prepared.densityIdentity] at alternativePhase
  exact ⟨referencePhase.trans alternativePhase.symm, alternativePhase⟩

end EulerNonuniqueness.Paper
