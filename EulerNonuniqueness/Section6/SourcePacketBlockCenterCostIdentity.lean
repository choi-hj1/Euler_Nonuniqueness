import EulerNonuniqueness.Section6.SourcePacketBlockCenterGeometry

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem SourcePacketBlockCenterNormalization.sourceCost_identity
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius : ℝ}
    {geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius}
    {reference : PatchMotion count} {receiver : Fin count} {phase : Fin count → ℝ}
    {outgoingPhase deformation : ℝ}
    (normalization : SourcePacketBlockCenterNormalization geometry reference receiver phase outgoingPhase deformation)
    (elapsed : ℝ) :
    let distance := ‖(scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ)‖ / 2
    geometry.sourceCost elapsed =
      (16384 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * deformation /
        (Real.pi * distance ^ 4) +
        3072 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * deformation /
          (Real.pi * distance ^ 4)) +
      (16 * scales.circulation (source.val + 1) / (Real.pi * distance ^ 3)) *
        ‖centroidAsymmetry family.patchMotion (start + elapsed) source‖ +
      (6 / (Real.pi * distance ^ 4)) *
        ‖(∫ position, quadrupoleDensity scales family.patchMotion (start + elapsed) source position •
          (position - quadrupoleCenter family.patchMotion (start + elapsed) source) ^ 2) - geometry.targetMoment elapsed‖ +
      22528 * scales.circulation (source.val + 1) * scales.omega (source.val + 1) ^ 2 * scales.length (source.val + 1) ^ 3 /
        (Real.pi * distance ^ 5) +
      768 * ‖geometry.targetMoment elapsed‖ *
        ‖(quadrupoleCenter family.patchMotion (start + elapsed) receiver -
          quadrupoleCenter family.patchMotion (start + elapsed) source) -
          ((scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ))‖ /
        (Real.pi * ‖(scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ)‖ ^ 5) := by
  dsimp only
  unfold SourcePacketPhysicalGeometry.sourceCost
  rw [normalization.location, normalization.firstCenter, normalization.secondCenter, normalization.deformationIdentity,
    normalization.observationDistance, normalization.gap, normalization.pairRadius, normalization.halfWidth,
    normalization.frozenDisplacement]
  simp only
  rw [source_packet_dipole_average_eq_center]
  ring

end EulerNonuniqueness.Paper

