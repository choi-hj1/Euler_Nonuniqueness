import EulerNonuniqueness.Section6.SourcePacketActualOutgoingCommonEnvelopeBudget
import EulerNonuniqueness.General.AffineLaplaceWindow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem Scales.eventually_actual_outgoing_common_envelope_subwindow (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ source : Fin count,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency}).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    let envelope := fun time => 4 * ‖centroidAsymmetry motion time source‖ +
      length * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
      changed.radius (source.val + 1) ^ 2
    Continuous envelope ∧ ∀ laterStart ∈ Icc start (start + horizon),
      ∀ finish ∈ Icc laterStart (start + horizon), ∀ weight : ℝ, 0 < weight →
      IntervalIntegrable (fun time => Real.exp (-weight * (time - laterStart)) * envelope time) volume laterStart finish ∧
      (∫ time in laterStart..finish, Real.exp (-weight * (time - laterStart)) * envelope time) ≤
        100000 * (changed.circulation (source.val + 1) / weight ^ 2 +
          (changed.circulation (source.val + 1) * (laterStart - start) + (1 + initialDistance) * length ^ 2 +
            ‖centroidAsymmetry motion start source‖) / weight) := by
  filter_upwards [scales.eventually_actual_outgoing_common_envelope_budget amplitudePositive ratioBound alphaPositive
    orbit sectionTime factorPositive factorSmall rootPositive boundaryNonnegative, eventually_gt_atTop (0 : ℝ)]
    with frequency factory frequencyPositive
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path source start horizon initialDistance
    startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let envelope := fun time => 4 * ‖centroidAsymmetry motion time source‖ +
    length * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ + changed.radius (source.val + 1) ^ 2
  have actual := factory count phase dipoleAngle prepared path source start horizon initialDistance
    startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper
  have shiftedIdentity (time : ℝ) : start + (time - start) = time := by ring
  have physicalContinuous : Continuous envelope := by
    have composed := actual.1.1.comp
      (show Continuous (fun time : ℝ => time - start) from continuous_id.sub continuous_const)
    simpa only [Function.comp_def, shiftedIdentity] using composed
  refine ⟨physicalContinuous, ?_⟩
  intro laterStart laterInside finish finishInside weight weightPositive
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationPositive : 0 < changed.circulation (source.val + 1) :=
    changed.circulation_pos frequencyPositive ratioPositive _
  have constantNonnegative : 0 ≤ 100000 * ((1 + initialDistance) * length ^ 2 + ‖centroidAsymmetry motion start source‖) := by
    have initialNonnegative : 0 ≤ initialDistance := by linarith only [initialLarge]
    positivity
  have majorized (time : ℝ) (inside : time ∈ Icc laterStart finish) : envelope time ≤
      (100000 * changed.circulation (source.val + 1)) * (time - start) +
        100000 * ((1 + initialDistance) * length ^ 2 + ‖centroidAsymmetry motion start source‖) := by
    have elapsedInside : time - start ∈ Icc 0 horizon :=
      ⟨by linarith only [inside.1, laterInside.1], by linarith only [inside.2, finishInside.2]⟩
    have bounded := actual.2 (time - start) elapsedInside
    calc
      _ ≤ 100000 * (changed.circulation (source.val + 1) * (time - start) +
          (1 + initialDistance) * length ^ 2 + ‖centroidAsymmetry motion start source‖) := by
        simpa only [shiftedIdentity] using bounded
      _ = _ := by ring
  have bound := intervalIntegral.integral_exp_neg_mul_le_of_affine_majorant physicalContinuous.continuousOn
    weightPositive (show 0 ≤ 100000 * changed.circulation (source.val + 1) by positivity)
    constantNonnegative laterInside.1 finishInside.1 majorized
  refine ⟨bound.1, bound.2.trans_eq ?_⟩
  ring

end EulerNonuniqueness.Paper
