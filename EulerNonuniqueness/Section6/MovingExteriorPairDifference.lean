import EulerNonuniqueness.Section6.MovingQuadrupoleFieldBounds
import EulerNonuniqueness.General.FiniteExteriorDifference

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.externalPatch_biotSavart_eq_sum_quadrupole
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (receiver : Fin count) (position : ℂ) :
    biotSavart (externalPatchVorticity scales motion time receiver) position =
      ∑ source ∈ Finset.univ.erase receiver, biotSavart (quadrupoleDensity scales motion time source) position := by
  rw [evolution.externalPatch_biotSavart_eq_sum inside receiver]
  exact Finset.sum_congr rfl (fun source _ =>
    (evolution.quadrupole_biotSavart_eq_sum_patch inside source position).symm)

theorem FinitePatchEvolution.externalPatch_biotSavart_receiver_difference_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (receiver source : Fin count) (different : receiver ≠ source)
    (distance : Fin count → ℝ) {crossDistance : ℝ} {first second : ℂ}
    (crossPositive : 0 < crossDistance)
    (positive : ∀ other ∈ (Finset.univ.erase receiver).erase source, 0 < distance other)
    (firstSeparated : ∀ other ∈ (Finset.univ.erase receiver).erase source, ∀ patch position,
      position ∈ motion.domain time other patch → distance other ≤ ‖first - position‖)
    (secondSeparated : ∀ other ∈ (Finset.univ.erase receiver).erase source, ∀ patch position,
      position ∈ motion.domain time other patch → distance other ≤ ‖second - position‖)
    (firstCrossSeparated : ∀ patch position, position ∈ motion.domain time source patch → crossDistance ≤ ‖first - position‖)
    (secondCrossSeparated : ∀ patch position, position ∈ motion.domain time receiver patch → crossDistance ≤ ‖second - position‖) :
    ‖biotSavart (externalPatchVorticity scales motion time receiver) first -
      biotSavart (externalPatchVorticity scales motion time source) second‖ ≤
      (∑ other ∈ (Finset.univ.erase receiver).erase source,
        2 * scales.circulation (other.val + 1) / (Real.pi * distance other ^ 2)) * ‖first - second‖ +
      2 * scales.circulation (source.val + 1) / (Real.pi * crossDistance) +
      2 * scales.circulation (receiver.val + 1) / (Real.pi * crossDistance) := by
  rw [evolution.externalPatch_biotSavart_eq_sum_quadrupole inside receiver first,
    evolution.externalPatch_biotSavart_eq_sum_quadrupole inside source second]
  have actual := EulerNonuniqueness.General.norm_sum_erase_sub_sum_erase_le receiver source different
    (fun other => biotSavart (quadrupoleDensity scales motion time other) first)
    (fun other => biotSavart (quadrupoleDensity scales motion time other) second)
  have common := Finset.sum_le_sum (s := (Finset.univ.erase receiver).erase source)
    (fun other member => (evolution.quadrupole_biotSavart_bounds_from_material_geometry inside amplitudePositive frequencyPositive ratioPositive
      other (positive other member) (firstSeparated other member) (secondSeparated other member)).2)
  rw [← Finset.sum_mul] at common
  have firstCross := (evolution.quadrupole_biotSavart_bounds_from_material_geometry inside amplitudePositive frequencyPositive ratioPositive
    source crossPositive firstCrossSeparated firstCrossSeparated).1
  have secondCross := (evolution.quadrupole_biotSavart_bounds_from_material_geometry inside amplitudePositive frequencyPositive ratioPositive
    receiver crossPositive secondCrossSeparated secondCrossSeparated).1
  exact actual.trans (add_le_add (add_le_add common firstCross) secondCross)

end EulerNonuniqueness.Paper
