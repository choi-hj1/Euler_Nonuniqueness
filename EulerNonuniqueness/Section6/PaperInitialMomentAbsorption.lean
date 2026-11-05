import EulerNonuniqueness.Section6.InitialMomentFrequencyAbsorption

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_initial_moment_weighted_seed_absorption
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation outgoingRadius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (source : Fin count)
    (firstCenter secondCenter firstSeparation secondSeparation displacement : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time source patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time source patch deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (outgoingRadiusLarge : 32 ≤ outgoingRadius) (ratioLarge : 96 * outgoingRadius ≤ scales.ratio)
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (centerBound : ‖firstCenter - secondCenter‖ ≤ (5 / 4 : ℝ) * scales.length (source.val + 1) * outgoingRadius)
    (firstBound : ‖firstSeparation‖ ≤ 2 * scales.length (source.val + 1))
    (secondBound : ‖secondSeparation‖ ≤ 2 * scales.length (source.val + 1))
    (distancePositive : 0 < ‖displacement‖) {positive : ℝ → ℂ}
    (positiveContinuous : Continuous positive) (positiveNonzero : ∀ parameter, positive parameter ≠ 0) :
    let moment := ∫ position, quadrupoleDensity scales motion time source position •
      (position - quadrupoleCenter motion time source) ^ 2
    let input := Section6.rhombusConstantMomentInput positive moment displacement
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    IntegrableOn (fun elapsed => Real.exp (-decay * elapsed) * input elapsed) (Ioi 0) ∧
      |∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * input elapsed| ≤
        (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * ‖displacement‖ ^ 4)) := by
  have momentBound := evolution.quadrupole_outgoing_initial_moment_bound inside amplitudePositive frequencyPositive
    ratioPositive source firstCenter secondCenter firstSeparation secondSeparation positionsEquation control
    deformationNonnegative deformationSmall (by linarith : 0 ≤ outgoingRadius) centerBound firstBound secondBound
  have weighted := Section6.rhombusConstantMomentInput_weighted_bound positiveContinuous positiveNonzero
    (∫ position, quadrupoleDensity scales motion time source position •
      (position - quadrupoleCenter motion time source) ^ 2) displacement
    (show 0 < 2 * Real.sqrt 2 * scales.omega source.val by
      exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
        (scales.omega_pos frequencyPositive ratioPositive source.val))
  exact ⟨weighted.1, weighted.2.trans (scales.initial_moment_weighted_cost_absorption source.val
    frequencyPositive ratioPositive distancePositive outgoingRadiusLarge ratioLarge radiusSmall
    deformationNonnegative deformationSmall _ momentBound)⟩

end EulerNonuniqueness.Paper
