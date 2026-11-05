import EulerNonuniqueness.Section6.SourcePacketPairedBlockInput
import EulerNonuniqueness.Section6.PaperExternalStrain

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def relativeBlockSourceShapeInput {count : ℕ} (scales : Scales) (alternative reference : PatchMotion count)
    (receiver source : Fin count) (time : ℝ) : ℝ × ℝ :=
  pointShapeForcingCLM (positiveHalfDiagonal reference time receiver, negativeHalfDiagonal reference time receiver)
    (complexStrainPair
      (vorticityComplexStrain (quadrupoleDensity scales alternative time source) (quadrupoleCenter alternative time receiver) -
        vorticityComplexStrain (quadrupoleDensity scales reference time source) (quadrupoleCenter reference time receiver))
      (positiveHalfDiagonal reference time receiver, negativeHalfDiagonal reference time receiver))

theorem quadrupoleRelativeLeadingStrain_eq_sum_actual_sources
    {count : ℕ} {scales : Scales} {alternative reference : PatchMotion count} {horizon time : ℝ}
    (alternativeEvolution : FinitePatchEvolution scales alternative horizon)
    (referenceEvolution : FinitePatchEvolution scales reference horizon) (inside : time ∈ Icc 0 horizon)
    (receiver : Fin count) {alternativeGap referenceGap : ℝ} (alternativePositive : 0 < alternativeGap)
    (referencePositive : 0 < referenceGap)
    (alternativeSeparated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch, ∀ location ∈ alternative.domain time source patch,
      alternativeGap ≤ ‖quadrupoleCenter alternative time receiver - location‖)
    (referenceSeparated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch, ∀ location ∈ reference.domain time source patch,
      referenceGap ≤ ‖quadrupoleCenter reference time receiver - location‖) :
    quadrupoleRelativeLeadingStrain scales alternative reference time receiver =
      ∑ source ∈ Finset.univ.erase receiver, relativeBlockSourceShapeInput scales alternative reference receiver source time := by
  unfold quadrupoleRelativeLeadingStrain quadrupoleExternalShapeStrain
  rw [alternativeEvolution.externalPatch_complexStrain_sum inside receiver (fun _ => alternativeGap)
      (fun _ _ => alternativePositive) alternativeSeparated,
    referenceEvolution.externalPatch_complexStrain_sum inside receiver (fun _ => referenceGap)
      (fun _ _ => referencePositive) referenceSeparated, ← Finset.sum_sub_distrib]
  have pairSum (values : Fin count → ℂ) (point : ℂ × ℂ) :
      complexStrainPair (∑ source ∈ Finset.univ.erase receiver, values source) point =
        ∑ source ∈ Finset.univ.erase receiver, complexStrainPair (values source) point := by
    have general (selected : Finset (Fin count)) :
        complexStrainPair (∑ source ∈ selected, values source) point =
          ∑ source ∈ selected, complexStrainPair (values source) point := by
      induction selected using Finset.induction_on with
      | empty => simp [complexStrainPair]
      | @insert source selected absent induction =>
        simp only [Finset.sum_insert absent]
        rw [← induction]
        ext <;> simp only [complexStrainPair, Prod.fst_add, Prod.snd_add, add_mul]
    exact general _
  rw [pairSum, map_sum]
  rfl

end EulerNonuniqueness.Paper
