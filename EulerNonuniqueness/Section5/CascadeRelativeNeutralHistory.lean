import EulerNonuniqueness.Section5.CascadeClosedSaddleDynamics
import EulerNonuniqueness.Section5.CascadeNeutralVelocity
import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments
import EulerNonuniqueness.Section6.MovingQuadrupoleEndpointMoment
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

def quadrupoleNeutralVelocity
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) : ℂ :=
  ((trajectory.velocity time).2.1 (finProdFinEquiv (index, 0)) +
    (trajectory.velocity time).2.1 (finProdFinEquiv (index, 1)) -
    (trajectory.velocity time).2.1 (finProdFinEquiv (index, 2)) -
    (trajectory.velocity time).2.1 (finProdFinEquiv (index, 3))) / 4

theorem quadrupoleNeutralVelocity_continuous
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) :
    Continuous (trajectory.quadrupoleNeutralVelocity index) := by
  have point (patch : Fin 4) : Continuous (fun time =>
      (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) :=
    (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp trajectory.velocity_continuous))
  exact (((point 0).add (point 1)).sub (point 2)).sub (point 3) |>.div_const 4

theorem centroidAsymmetry_hasDerivAt_quadrupoleNeutralVelocity
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    (index : Fin count) {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) :
    HasDerivAt (fun current => centroidAsymmetry trajectory.movingFamily.patchMotion current index)
      (trajectory.quadrupoleNeutralVelocity index time) time := by
  have point (patch : Fin 4) : HasDerivAt
      (fun current => patchCentroid trajectory.movingFamily.patchMotion current index patch)
      ((trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) time := by
    apply (trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) time).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact (trajectory.cascadeCenters_eq_patchCentroid initialCircles member index patch).symm
  exact ((((point 0).add (point 1)).sub (point 2)).sub (point 3)).div_const 4

end MovingCentroidGaugeTrajectory

def quadrupoleNeutralExternalVelocity {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℂ :=
  (4 * scales.circulation (index.val + 1))⁻¹ •
    ∫ position, quadrupoleDensity scales motion time index position •
      biotSavart (externalPatchVorticity scales motion time index) position

theorem FiniteMovingPatchFamily.centroidAsymmetry_hasDerivAt_literal_external
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label)) (index : Fin count) :
    HasDerivAt (fun current => centroidAsymmetry family.patchMotion current index)
      (quadrupoleNeutralExternalVelocity scales family.patchMotion index time) time := by
  have derivative := family.centroidAsymmetry_hasDerivAt_external_closed scales densityEquation evolution
    horizonPositive timeInside amplitudePositive frequencyPositive ratioPositive inside material index
  have fieldIdentity (position : ℂ) : biotSavart (family.vorticity time) position -
      biotSavart (quadrupoleDensity scales family.patchMotion time index) position =
      biotSavart (externalPatchVorticity scales family.patchMotion time index) position := by
    rw [← family.patchVorticity_eq scales densityEquation,
      evolution.patchVorticity_biotSavart_internal_external timeInside index position,
      evolution.quadrupole_biotSavart_eq_sum_patch timeInside index position]
    abel
  simpa only [quadrupoleNeutralExternalVelocity, fieldIdentity] using derivative

namespace CascadeMaterialPreparedPair

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}

def pairedNeutralVelocity
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) : Fin count → ℝ → ℂ :=
  Fin.cases prepared.trajectory.quadrupoleNeutralVelocity
    (fun _ => prepared.referenceWitness.trajectory.quadrupoleNeutralVelocity) side

theorem pairedNeutralVelocity_continuous
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) (index : Fin count) :
    Continuous (prepared.pairedNeutralVelocity side index) := by
  fin_cases side <;> exact MovingCentroidGaugeTrajectory.quadrupoleNeutralVelocity_continuous _ index

theorem paired_neutral_hasDerivAt
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) (index : Fin count)
    {time : ℝ} (inside : time ∈ Ioo (-(1 : ℝ)) 3) :
    HasDerivAt (fun current => centroidAsymmetry (cascadePairedMotion prepared side) current index)
      (prepared.pairedNeutralVelocity side index time) time := by
  fin_cases side
  · exact prepared.trajectory.centroidAsymmetry_hasDerivAt_quadrupoleNeutralVelocity (fun _ => rfl) index inside
  · simpa only [cascadePairedMotion, pairedNeutralVelocity, Fin.cases_succ, prepared.referenceIdentity] using
      prepared.referenceWitness.trajectory.centroidAsymmetry_hasDerivAt_quadrupoleNeutralVelocity
        (fun _ => rfl) index inside

end CascadeMaterialPreparedPair

theorem CascadeInternallyStoppedPath.paired_neutralVelocity_eq_external
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (side : Fin 2) (index : Fin count)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) :
    prepared.pairedNeutralVelocity side index time =
      quadrupoleNeutralExternalVelocity scales (cascadePairedMotion prepared side) index time := by
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have geometric := prepared.paired_neutral_hasDerivAt side index globalInside
  apply geometric.unique
  fin_cases side
  · apply prepared.trajectory.movingFamily.centroidAsymmetry_hasDerivAt_literal_external scales
      prepared.densityIdentity path.evolution path.stopPositive inside amplitudePositive frequencyPositive ratioPositive
      (fun _ => globalInside) ?_ index
    intro label angle
    rw [← prepared.trajectory.movingFamily.patchVorticity_eq scales prepared.densityIdentity]
    exact path.material_boundary inside label angle
  · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity]
    apply prepared.referenceWitness.trajectory.movingFamily.centroidAsymmetry_hasDerivAt_literal_external scales
      prepared.referenceWitness.densityIdentity
      (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound]))
      path.stopPositive inside amplitudePositive frequencyPositive ratioPositive (fun _ => globalInside) ?_ index
    intro label angle
    exact prepared.referenceWitness.trajectory.movingFamily_material_equation_of_margin
      prepared.referenceWitness.marginPositive globalInside
      (prepared.referenceWitness.safe time ⟨inside.1, by linarith [inside.2, path.stopBound]⟩) label angle

theorem CascadeInternallyStoppedPath.relative_neutral_original_history
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (nonterminal : index.val + 1 < count)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) :
    centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index -
      centroidAsymmetry prepared.reference time index =
    ∫ current in (0 : ℝ)..time,
      quadrupoleNeutralExternalVelocity scales prepared.trajectory.movingFamily.patchMotion index current -
        quadrupoleNeutralExternalVelocity scales prepared.reference index current := by
  have initial : centroidAsymmetry prepared.trajectory.movingFamily.patchMotion 0 index -
      centroidAsymmetry prepared.reference 0 index = 0 := by
    simp only [centroidAsymmetry, prepared.nonterminal_initial_centroid index nonterminal, sub_self]
  have continuous := (prepared.pairedNeutralVelocity_continuous 0 index).sub
    (prepared.pairedNeutralVelocity_continuous 1 index)
  have derivative (current : ℝ) (member : current ∈ Icc 0 time) :=
    (prepared.paired_neutral_hasDerivAt 0 index
      (show current ∈ Ioo (-(1 : ℝ)) 3 from ⟨by linarith [member.1], by linarith [member.2, inside.2, path.stopBound]⟩)).sub
    (prepared.paired_neutral_hasDerivAt 1 index
      (show current ∈ Ioo (-(1 : ℝ)) 3 from ⟨by linarith [member.1], by linarith [member.2, inside.2, path.stopBound]⟩))
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
    (fun current member => (derivative current member).continuousAt.continuousWithinAt)
    (fun current member => derivative current ⟨member.1.le, member.2.le⟩)
    (continuous.intervalIntegrable 0 time)
  have integralEquality : (∫ current in (0 : ℝ)..time,
      prepared.pairedNeutralVelocity 0 index current - prepared.pairedNeutralVelocity 1 index current) =
      ∫ current in (0 : ℝ)..time,
        quadrupoleNeutralExternalVelocity scales prepared.trajectory.movingFamily.patchMotion index current -
          quadrupoleNeutralExternalVelocity scales prepared.reference index current := by
    apply intervalIntegral.integral_congr
    intro current member
    have closed : current ∈ Icc 0 path.stop :=
      ⟨(uIcc_of_le inside.1 ▸ member).1, (uIcc_of_le inside.1 ▸ member).2.trans inside.2⟩
    dsimp only
    rw [path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 0 index closed,
      path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 1 index closed]
    rfl
  change (∫ current in (0 : ℝ)..time,
      prepared.pairedNeutralVelocity 0 index current - prepared.pairedNeutralVelocity 1 index current) =
    centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index -
      centroidAsymmetry prepared.reference time index -
        (centroidAsymmetry prepared.trajectory.movingFamily.patchMotion 0 index -
          centroidAsymmetry prepared.reference 0 index) at identity
  rw [initial, sub_zero] at identity
  exact identity.symm.trans integralEquality

theorem CascadeInternallyStoppedPath.relative_neutral_external_continuousOn
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    ContinuousOn (fun time =>
      quadrupoleNeutralExternalVelocity scales prepared.trajectory.movingFamily.patchMotion index time -
        quadrupoleNeutralExternalVelocity scales prepared.reference index time) (Icc 0 path.stop) := by
  apply ((prepared.pairedNeutralVelocity_continuous 0 index).sub
    (prepared.pairedNeutralVelocity_continuous 1 index)).continuousOn.congr
  intro time inside
  dsimp only
  rw [path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 0 index inside,
    path.paired_neutralVelocity_eq_external amplitudePositive frequencyPositive ratioPositive 1 index inside]
  rfl

theorem CascadeInternallyStoppedPath.relative_neutral_original_history_norm
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (nonterminal : index.val + 1 < count)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) :
    ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index -
      centroidAsymmetry prepared.reference time index‖ ≤
    ∫ current in (0 : ℝ)..time,
      ‖quadrupoleNeutralExternalVelocity scales prepared.trajectory.movingFamily.patchMotion index current -
        quadrupoleNeutralExternalVelocity scales prepared.reference index current‖ := by
  rw [path.relative_neutral_original_history amplitudePositive frequencyPositive ratioPositive index nonterminal inside]
  exact intervalIntegral.norm_integral_le_integral_norm inside.1

end EulerNonuniqueness.Paper
