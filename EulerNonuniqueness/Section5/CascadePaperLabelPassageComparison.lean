import EulerNonuniqueness.Section5.CascadeNormalizedPointRegularity
import EulerNonuniqueness.Section5.CascadeNormalizedForcingBound
import EulerNonuniqueness.Section6.CenteredPassageLinearForcing
import EulerNonuniqueness.Section6.SeparatingOrbitUniformGap
import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_material_paper_label_passage_comparison (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime incomingTime horizon : ℝ)
    (horizonPositive : 0 < horizon)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∃ gap > (0 : ℝ), ∃ referenceBound ≥ (0 : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ start window : ℝ,
    0 < window → window ≤ horizon →
    ∀ rotation : ℂ, ‖rotation‖ = 1 →
    (∀ time ∈ Icc 0 window, start + time / ({scales with frequency := frequency} : Scales).omega (index.val + 1) ∈ Icc 0 path.stop) →
    ∀ time ∈ Icc 0 window,
      ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
          index start rotation time - centrallySymmetricFourPoint (orbit.positive (time + incomingTime))
            (orbit.negative (time + incomingTime))‖ ≤
        (‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
            index start rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ +
          (referenceBound + 1) * time / (2048 * ({scales with frequency := frequency} : Scales).omega (index.val + 1))) *
          Real.exp ((16 / gap ^ 2 + 1 / (2048 * ({scales with frequency := frequency} : Scales).omega (index.val + 1))) * time) := by
  obtain ⟨referenceGap, referenceGapPositive, separated⟩ := normalizedSeparatingOrbit_uniform_pair_gap orbit normalized
  let gap := min factor referenceGap
  have gapPositive : 0 < gap := lt_min factorPositive referenceGapPositive
  let reference : ℝ → FourPointConfiguration := fun time =>
    centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime))
  have referenceDerivative (time : ℝ) : HasDerivAt reference (fourPointCenteredField 1 (reference time)) time := by
    have properties := normalizedSeparatingOrbit_full_point_equation orbit normalized (time + incomingTime)
    have permuted := relabelNegativePoints_hasDerivAt properties.1
    have actual := permuted.scomp time ((hasDerivAt_id time).add_const incomingTime)
    have noncollision := relabelNegativePoints_noncollision properties.2
    simp only [relabelNegativePoints_central, neg_neg] at noncollision
    have central := fourPointCenteredField_central 1 noncollision
    simp only [relabelNegativePoints_central, neg_neg] at actual central
    change fourPointCenteredField 1 (reference time) = fourPointField 1 (reference time) at central
    rw [central]
    simpa only [one_smul, Function.comp_def] using actual
  have referenceContinuous : ContinuousOn reference (Icc 0 horizon) :=
    fun time _ => (referenceDerivative time).continuousAt.continuousWithinAt
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn referenceContinuous
  let referenceBound := max bound 0
  refine ⟨gap, gapPositive, referenceBound, le_max_right _ _, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_material_normalized_point_forcing_bound amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative] with frequency frequencyOne forcing
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start window windowPositive windowBound rotation rotationNorm inside
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have actual := centered_passage_linear_forcing_error windowPositive gapPositive
    (by positivity : 0 ≤ 1 / (2048 * changed.omega (index.val + 1))) (le_max_right bound 0)
    (path.normalizedPoint_continuousOn index start rotation inside)
    (referenceContinuous.mono (Icc_subset_Icc_right windowBound))
    (path.normalizedPointForcing_continuousOn frequencyPositive ratioPositive factorPositive index start rotationNorm inside)
    (fun time member => path.normalizedPoint_equation frequencyPositive ratioPositive index start time rotationNorm
      (inside time ⟨member.1.le, member.2.le⟩))
    (fun time _ => referenceDerivative time)
    (fun time member target source different => (min_le_left _ _).trans
      (path.normalizedPoint_pair_gap index start time rotationNorm (inside time member) target source different.symm))
    (fun time member target source different => (min_le_right _ _).trans
      (by
        have bound := separated (time + incomingTime) (negativeLabelSwap target) (negativeLabelSwap source)
          (fun equal => different (negativeLabelSwap.injective equal).symm)
        have identity := relabelNegativePoints_central (orbit.positive (time + incomingTime)) (-orbit.negative (time + incomingTime))
        have first := congrFun identity target
        have second := congrFun identity source
        simp only [relabelNegativePoints, neg_neg] at first second
        rw [first, second] at bound
        exact bound))
    (fun time member => (bounded time ⟨member.1, member.2.trans windowBound⟩).trans (le_max_left _ _))
    (fun time member => forcing count phase dipoleAngle prepared path index start time rotation rotationNorm (inside time member))
  intro time member
  have result := actual time member
  have scalar (initial omega : ℝ) :
      (initial + 1 / (2048 * omega) * (referenceBound + 1) * time) =
        initial + (referenceBound + 1) * time / (2048 * omega) := by ring
  simp only [reference, zero_add, abs_one, mul_one] at result
  rw [scalar] at result
  exact result

end EulerNonuniqueness.Paper

