import EulerNonuniqueness.Section6.SourcePacketBlockCenterLeadingInput
import EulerNonuniqueness.Section6.SourcePacketReferenceBlockInputBudget

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem SourcePacketBlockCenterNormalization.paired_source_input_identity
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius : ℝ}
    {geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius}
    {reference : PatchMotion count} {receiver : Fin count} {phase : Fin count → ℝ}
    {outgoingPhase deformation : ℝ}
    (normalization : SourcePacketBlockCenterNormalization geometry reference receiver phase outgoingPhase deformation)
    (elapsed : ℝ) :
    (pointShapeForcingCLM
      (positiveHalfDiagonal reference (start + elapsed) receiver, negativeHalfDiagonal reference (start + elapsed) receiver)
      (complexStrainPair
        (vorticityComplexStrain (quadrupoleDensity scales family.patchMotion (start + elapsed) source)
            (quadrupoleCenter family.patchMotion (start + elapsed) receiver) -
          vorticityComplexStrain (quadrupoleDensity scales reference (start + elapsed) source)
            (quadrupoleCenter reference (start + elapsed) receiver))
        (positiveHalfDiagonal reference (start + elapsed) receiver, negativeHalfDiagonal reference (start + elapsed) receiver))).1 =
      geometry.actualInput elapsed - referenceBlockSourceInput scales reference receiver source (start + elapsed) := by
  rw [reference_frame_source_strain_difference_input, normalization.actualInput_identity]
  rfl

end EulerNonuniqueness.Paper
