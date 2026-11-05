import EulerNonuniqueness.Section5.CascadePassageShadowing
import EulerNonuniqueness.Section5.CascadePaperLabelPassageGap
import EulerNonuniqueness.Section5.CascadeAccurateOutgoingData
import EulerNonuniqueness.Section5.CascadeOutgoingInternalGap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_material_matched_passage_continuation (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime incomingTime outgoingTime : ℝ)
    (timeOrder : incomingTime < outgoingTime)
    {factor threshold scaleRoot boundaryConstant error : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (errorPositive : 0 < error) (errorSmall : error ≤ 1 / 64)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖)
    (distanceLarge : 512 ≤ separationRadius orbit outgoingTime)
    (separationClose : ‖orbit.positive outgoingTime + orbit.negative outgoingTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ error / 2)
    (referenceOutgoing : (7 / 8 : ℝ) * separationRadius orbit outgoingTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive outgoingTime - orbit.negative outgoingTime)).re) :
    ∃ tolerance > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ start : ℝ,
    0 ≤ start → start ≤ path.stop → ∀ rotation : ℂ, ‖rotation‖ = 1 →
    ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
      index start rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance →
    ∀ time ∈ Icc start path.stop, ∀ first second : Fin 4, first ≠ second →
      factor * ({scales with frequency := frequency} : Scales).length (index.val + 1) <
        ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index first -
          patchCentroid prepared.trajectory.movingFamily.patchMotion time index second‖ := by
  let horizon := outgoingTime - incomingTime
  have horizonPositive : 0 < horizon := sub_pos.mpr timeOrder
  have factorOne : factor ≤ 1 := by linarith
  obtain ⟨gapTolerance, gapTolerancePositive, gapImprovement⟩ :=
    scales.eventually_material_paper_label_passage_strict_gap amplitudePositive ratioBound alphaPositive orbit normalized
      sectionTime incomingTime horizon horizonPositive factorPositive factorOne referenceSeparated rootPositive boundaryNonnegative
  obtain ⟨shadowTolerance, shadowTolerancePositive, shadowing⟩ :=
    scales.eventually_material_paper_label_passage_shadowing amplitudePositive ratioBound alphaPositive orbit normalized
      sectionTime incomingTime horizon horizonPositive (error / 4) (by positivity) factorPositive factorOne
      rootPositive boundaryNonnegative
  let tolerance := min gapTolerance (min shadowTolerance (factor / 4))
  have tolerancePositive : 0 < tolerance := lt_min gapTolerancePositive
    (lt_min shadowTolerancePositive (by positivity))
  refine ⟨tolerance, tolerancePositive, ?_⟩
  filter_upwards [gapImprovement, shadowing,
    scales.eventually_material_outgoing_internal_gap amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (16 * separationRadius orbit outgoingTime)]
    with frequency gapImprovement shadowing outgoing frequencyOne frequencyDistance
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start startNonnegative startBound
    rotation rotationNorm initial time member first second different
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have initialGap : ‖cascadeNormalizedPointPositions changed motion index start rotation 0 -
      centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ gapTolerance :=
    initial.trans (min_le_left _ _)
  have initialShadow : ‖cascadeNormalizedPointPositions changed motion index start rotation 0 -
      centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ shadowTolerance :=
    initial.trans ((min_le_right _ _).trans (min_le_left _ _))
  have insideWindow {window : ℝ} (endBound : start + window / omega ≤ path.stop)
      (current : ℝ) (currentInside : current ∈ Icc 0 window) : start + current / omega ∈ Icc 0 path.stop := by
    constructor
    · exact add_nonneg startNonnegative (div_nonneg currentInside.1 omegaPositive.le)
    · exact (add_le_add_left (div_le_div_of_nonneg_right currentInside.2 omegaPositive.le) start).trans endBound
  by_cases atStart : time = start
  · subst time
    have close : ‖cascadeNormalizedPointPositions changed motion index start rotation 0 -
        centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < factor / 2 := by
      have small := initial.trans ((min_le_right _ _).trans (min_le_right _ _))
      linarith
    have actual := cascadeNormalizedPointPositions_strict_gap_physical changed motion index start 0 rotationNorm
      (fun target source different => by
        have gap := configuration_pair_gap_of_close close
          (fun target source different => by linarith [referenceSeparated incomingTime target source different])
          target source different
        simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using gap) first second different.symm
    simpa only [zero_div, add_zero] using actual
  have timePositive : start < time := lt_of_le_of_ne member.1 (Ne.symm atStart)
  let fastTime := omega * (time - start)
  have fastPositive : 0 < fastTime := mul_pos omegaPositive (sub_pos.mpr timePositive)
  have physicalIdentity : start + fastTime / omega = time := by dsimp only [fastTime]; field_simp
  by_cases beforeOutgoing : fastTime ≤ horizon
  · have actual := gapImprovement count phase dipoleAngle prepared path index start fastTime fastPositive beforeOutgoing
      rotation rotationNorm (insideWindow (by rw [physicalIdentity]; exact member.2)) initialGap fastTime
      ⟨fastPositive.le, le_rfl⟩
    have physical := cascadeNormalizedPointPositions_strict_gap_physical changed motion index start fastTime rotationNorm
      actual first second different.symm
    change factor * length < ‖patchCentroid motion (start + fastTime / omega) index first -
      patchCentroid motion (start + fastTime / omega) index second‖ at physical
    rw [physicalIdentity] at physical
    exact physical
  have horizonBound : start + horizon / omega ≤ time := by
    rw [← physicalIdentity]
    exact add_le_add_left (div_le_div_of_nonneg_right (le_of_not_ge beforeOutgoing) omegaPositive.le) start
  have close := shadowing count phase dipoleAngle prepared path index start horizon horizonPositive le_rfl
    rotation rotationNorm (insideWindow (horizonBound.trans member.2)) initialShadow horizon ⟨horizonPositive.le, le_rfl⟩
  have orbitTime : horizon + incomingTime = outgoingTime := by dsimp only [horizon]; ring
  rw [orbitTime] at close
  have initialOutgoing := cascadeNormalizedPointPositions_outgoing_data_with_error changed motion index start horizon
    errorPositive.le errorSmall rotationNorm (by simp [Complex.norm_exp, Complex.mul_re])
    distanceLarge separationClose referenceOutgoing close.le
  let entry := start + horizon / omega
  let direction := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
  have entryNonnegative : 0 ≤ entry := add_nonneg startNonnegative (div_nonneg horizonPositive.le omegaPositive.le)
  have entryBound : entry ≤ time := horizonBound
  have distanceSmall : separationRadius orbit outgoingTime ≤ omega / 16 := by
    have omegaLower := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (index.val + 1)
    dsimp only [omega]
    linarith
  have continued := outgoing count phase dipoleAngle prepared path index entry (time - entry)
    (separationRadius orbit outgoingTime) entryNonnegative (sub_nonneg.mpr entryBound)
    (by linarith [member.2, path.stopBound]) (by simpa using member.2) distanceLarge distanceSmall direction
    (by simp [direction, norm_mul, rotationNorm, Complex.norm_exp, Complex.mul_re])
  dsimp only at initialOutgoing continued
  have firstInitial := initialOutgoing.1.trans
    (mul_le_mul_of_nonneg_right errorSmall lengthPositive.le)
  have secondInitial := initialOutgoing.2.1.trans
    (mul_le_mul_of_nonneg_right errorSmall lengthPositive.le)
  have continued := continued (by convert firstInitial using 1 <;> ring)
    (by convert secondInitial using 1 <;> ring) initialOutgoing.2.2.1 initialOutgoing.2.2.2
    (time - entry) ⟨sub_nonneg.mpr entryBound, le_rfl⟩ first second different
  have strict : factor * length < length / 2 := by nlinarith
  exact strict.trans_le (by simpa only [add_sub_cancel] using continued)

end EulerNonuniqueness.Paper
