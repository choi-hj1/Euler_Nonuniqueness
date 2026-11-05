import EulerNonuniqueness.Section5.CascadeStoppedPatchErrorBound

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_stopped_patch_error_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {scaleRoot boundaryConstant factor tolerance : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {threshold referenceConstant shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
      ‖quadrupoleDilationPatchError {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time‖ /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ≤ tolerance := by
  obtain ⟨constant, constantOne, estimates⟩ := exists_uniform_cascade_stopped_patch_error_bound factorPositive factorSmall
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2 * constant / (scales.amplitude * tolerance)),
    estimates scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative]
    with frequency frequencyOne frequencyLarge actual
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius monitor count prepared path time inside index
  have actualBound := actual prepared path time inside index
  dsimp only at actualBound
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaFrequency : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _
  have omegaOne : 1 ≤ omega := frequencyOne.trans omegaFrequency
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have lengthPositive : 0 < length := changed.length_pos _
  have identity : constant * omega * (changed.radius (index.val + 1) ^ 2 / length ^ 2) =
      2 * constant / (scales.amplitude * omega ^ 2) := by
    rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
    change constant * omega * ((2 * length ^ 2 / (scales.amplitude * omega ^ 3)) / length ^ 2) = _
    field_simp [lengthPositive.ne', omegaPositive.ne', amplitudePositive.ne']
    <;> ring
  have scaled : 2 * constant ≤ scales.amplitude * tolerance * omega := by
    simpa only [mul_comm] using
      (div_le_iff₀ (mul_pos amplitudePositive tolerancePositive)).mp (frequencyLarge.trans omegaFrequency)
  have omegaSquare : omega ≤ omega ^ 2 := by nlinarith
  have enlarged := scaled.trans (mul_le_mul_of_nonneg_left omegaSquare
    (mul_nonneg amplitudePositive.le tolerancePositive.le))
  have budget : 2 * constant / (scales.amplitude * omega ^ 2) ≤ tolerance := by
    apply (div_le_iff₀ (mul_pos amplitudePositive (sq_pos_of_pos omegaPositive))).mpr
    nlinarith
  change ‖quadrupoleDilationPatchError changed prepared.trajectory.movingFamily.patchMotion index time‖ / length ≤ _ at actualBound ⊢
  rw [identity] at actualBound
  exact actualBound.trans budget

end EulerNonuniqueness.Paper
