import EulerNonuniqueness.Section6.SourcePacketSignedTail
import EulerNonuniqueness.Section6.PaperInitialMomentAbsorption

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem SourcePacketPhysicalGeometry.inherited_moment_seed_absorption
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius outgoingRadius : ℝ}
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    (horizonNonnegative : 0 ≤ horizon)
    (outgoingRadiusLarge : 32 ≤ outgoingRadius) (ratioLarge : 96 * outgoingRadius ≤ scales.ratio)
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (widthSmall : geometry.halfWidth ≤ scales.length (source.val + 1))
    (pairSmall : geometry.pairRadius ≤ (5 / 4 : ℝ) * scales.length (source.val + 1) * outgoingRadius) :
    let inheritedMoment := ∫ position, quadrupoleDensity scales family.patchMotion start source position •
      (position - quadrupoleCenter family.patchMotion start source) ^ 2
    6 * ‖inheritedMoment‖ /
      (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4 * (2 * Real.sqrt 2 * scales.omega source.val)) ≤
        (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * ‖geometry.frozenDisplacement‖ ^ 4)) := by
  have zeroInside : (0 : ℝ) ∈ Icc 0 horizon := ⟨le_rfl, horizonNonnegative⟩
  have positions := geometry.positions 0 zeroInside
  have control := geometry.control 0 zeroInside
  have timeRange := geometry.timeRange 0 zeroInside
  simp only [add_zero] at positions control timeRange
  have momentBound := geometry.evolution.quadrupole_outgoing_initial_moment_bound timeRange
    geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive source
    (geometry.firstCenter 0) (geometry.secondCenter 0) (geometry.firstSeparation 0) (geometry.secondSeparation 0)
    positions control geometry.deformationNonnegative geometry.deformationSmall
    (by linarith : 0 ≤ outgoingRadius)
    ((geometry.pairUpper 0 zeroInside).trans pairSmall)
    ((geometry.firstBound 0 zeroInside).trans (by linarith))
    ((geometry.secondBound 0 zeroInside).trans (by linarith))
  exact scales.initial_moment_weighted_cost_absorption source.val geometry.frequencyPositive geometry.ratioPositive
    (norm_pos_iff.mpr geometry.frozenNonzero) outgoingRadiusLarge ratioLarge radiusSmall
    geometry.deformationNonnegative geometry.deformationSmall _ momentBound

end EulerNonuniqueness.Paper
