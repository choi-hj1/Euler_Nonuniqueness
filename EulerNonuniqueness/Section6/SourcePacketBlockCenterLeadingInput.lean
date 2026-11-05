import EulerNonuniqueness.Section6.SourcePacketBlockCenterGeometry
import EulerNonuniqueness.Section6.PaperActualRelativeStrainForcing

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem SourcePacketBlockCenterNormalization.actualInput_identity
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius : ℝ}
    {geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius}
    {reference : PatchMotion count} {receiver : Fin count} {phase : Fin count → ℝ}
    {outgoingPhase deformation : ℝ}
    (normalization : SourcePacketBlockCenterNormalization geometry reference receiver phase outgoingPhase deformation)
    (elapsed : ℝ) :
    geometry.actualInput elapsed =
      (pointShapeForcingCLM (positiveHalfDiagonal reference (start + elapsed) receiver,
          negativeHalfDiagonal reference (start + elapsed) receiver)
        (complexStrainPair
          (vorticityComplexStrain (quadrupoleDensity scales family.patchMotion (start + elapsed) source)
            (quadrupoleCenter family.patchMotion (start + elapsed) receiver))
          (positiveHalfDiagonal reference (start + elapsed) receiver,
            negativeHalfDiagonal reference (start + elapsed) receiver))).1 := by
  unfold SourcePacketPhysicalGeometry.actualInput SourcePacketPhysicalGeometry.actualStrain
  rw [normalization.location, normalization.positive, normalization.negative]
  rfl

theorem reference_frame_source_strain_difference_input (positive negative alternativeStrain referenceStrain : ℂ) :
    (pointShapeForcingCLM (positive, negative)
      (complexStrainPair (alternativeStrain - referenceStrain) (positive, negative))).1 =
      (pointShapeForcingCLM (positive, negative) (complexStrainPair alternativeStrain (positive, negative))).1 -
        (pointShapeForcingCLM (positive, negative) (complexStrainPair referenceStrain (positive, negative))).1 := by
  have identity : complexStrainPair (alternativeStrain - referenceStrain) (positive, negative) =
      complexStrainPair alternativeStrain (positive, negative) - complexStrainPair referenceStrain (positive, negative) := by
    ext <;> simp only [complexStrainPair, Prod.fst_sub, Prod.snd_sub, sub_mul]
  rw [identity, map_sub]
  rfl

end EulerNonuniqueness.Paper
