import EulerNonuniqueness.Section1.CirculationPairStrain
import EulerNonuniqueness.Section1.ForeignInteractionWeight
import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem FinitePatchEvolution.quadrupole_biotSavart_bounds
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) {first second : ℂ} {distance : ℝ}
    (positive : 0 < distance)
    (firstSeparated : ∀ patch, ∀ location ∈ motion.domain time index patch, distance ≤ ‖first - location‖)
    (secondSeparated : ∀ patch, ∀ location ∈ motion.domain time index patch, distance ≤ ‖second - location‖) :
    ‖biotSavart (quadrupoleDensity scales motion time index) first‖ ≤
        2 * scales.circulation (index.val + 1) / (Real.pi * distance) ∧
      ‖biotSavart (quadrupoleDensity scales motion time index) first -
          biotSavart (quadrupoleDensity scales motion time index) second‖ ≤
        (2 * scales.circulation (index.val + 1) / (Real.pi * distance ^ 2)) * ‖first - second‖ := by
  have individual (patch : Fin 4) := evolution.patch_biotSavart_bounds inside amplitudePositive frequencyPositive
    ratioPositive index patch positive (firstSeparated patch) (secondSeparated patch)
  rw [evolution.quadrupole_biotSavart_eq_sum_patch inside index first,
    evolution.quadrupole_biotSavart_eq_sum_patch inside index second]
  constructor
  · exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => (individual patch).1)).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring))
  · rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => (individual patch).2)).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring))

theorem FinitePatchEvolution.reference_relative_external_field_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (center : Fin count → ℂ)
    (separated : ∀ receiver source, receiver ≠ source → ∀ patch, ∀ location ∈ motion.domain time source patch,
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8 ≤ ‖center receiver - location‖)
    (first second : Fin count) (different : first ≠ second) :
    ‖biotSavart (externalPatchVorticity scales motion time first) (center first) -
        biotSavart (externalPatchVorticity scales motion time second) (center second)‖ ≤
      (2304 / Real.pi) * scales.strain * ‖center first - center second‖ +
        (144 / Real.pi) * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
  classical
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  let field := fun source : Fin count => biotSavart (quadrupoleDensity scales motion time source)
  let distance := fun receiver source : Fin count =>
    |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8
  let weight := fun receiver source : Fin count =>
    2 * scales.circulation (source.val + 1) / (Real.pi * distance receiver source ^ 2)
  let common := (Finset.univ.erase first).erase second
  have distancePositive (receiver source : Fin count) (different : receiver ≠ source) : 0 < distance receiver source := by
    exact div_pos (scales.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality))))
      (by norm_num)
  have weightNonnegative (receiver source : Fin count) : 0 ≤ weight receiver source :=
    div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  have externalIdentity (receiver : Fin count) (position : ℂ) :
      biotSavart (externalPatchVorticity scales motion time receiver) position =
        ∑ source ∈ Finset.univ.erase receiver, field source position := by
    rw [evolution.externalPatch_biotSavart_eq_sum inside receiver position]
    exact Finset.sum_congr rfl fun source _ => (evolution.quadrupole_biotSavart_eq_sum_patch inside source position).symm
  have commonBound (source : Fin count) (member : source ∈ common) :
      ‖field source (center first) - field source (center second)‖ ≤
        (weight first source + weight second source) * ‖center first - center second‖ := by
    have notSecond := (Finset.mem_erase.mp member).1
    have notFirst := (Finset.mem_erase.mp (Finset.mem_erase.mp member).2).1
    rcases le_total (distance first source) (distance second source) with ordered | ordered
    · have estimate := (evolution.quadrupole_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive
        source (distancePositive first source (Ne.symm notFirst)) (separated first source (Ne.symm notFirst))
        (fun patch location locationInside => ordered.trans (separated second source (Ne.symm notSecond) patch location locationInside))).2
      exact estimate.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (weightNonnegative second source)) (norm_nonneg _))
    · have estimate := (evolution.quadrupole_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive
        source (distancePositive second source (Ne.symm notSecond))
        (fun patch location locationInside => ordered.trans (separated first source (Ne.symm notFirst) patch location locationInside))
        (separated second source (Ne.symm notSecond))).2
      exact estimate.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (weightNonnegative first source)) (norm_nonneg _))
  have firstSubset : common ⊆ Finset.univ.erase first := Finset.erase_subset _ _
  have secondSubset : common ⊆ Finset.univ.erase second := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp member).1, Finset.mem_univ _⟩
  have firstSum := (Finset.sum_le_sum_of_subset_of_nonneg firstSubset
    (fun source _ _ => weightNonnegative first source)).trans
      (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive first)
  have secondSum := (Finset.sum_le_sum_of_subset_of_nonneg secondSubset
    (fun source _ _ => weightNonnegative second source)).trans
      (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive second)
  have commonSumBound : ‖∑ source ∈ common, (field source (center first) - field source (center second))‖ ≤
      (2304 / Real.pi) * scales.strain * ‖center first - center second‖ := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum commonBound).trans
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    exact (mul_le_mul_of_nonneg_right (add_le_add firstSum secondSum) (norm_nonneg _)).trans_eq (by ring)
  have gapPositive : 0 < |scales.location (first.val + 1) - scales.location (second.val + 1)| :=
    scales.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have crossFirst := (evolution.quadrupole_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive second
    (distancePositive first second different) (separated first second different) (separated first second different)).1
  have crossSecond := (evolution.quadrupole_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive first
    (distancePositive second first (Ne.symm different)) (separated second first (Ne.symm different))
    (separated second first (Ne.symm different))).1
  have massBound := scales.circulation_pair_le_strain_distance_sq frequencyBound ratioBound alphaPositive
    first.val second.val (fun equality => different (Fin.ext equality))
  have mutualBound : ‖field second (center first) - field first (center second)‖ ≤
      (144 / Real.pi) * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
    apply (norm_sub_le _ _).trans
    apply (add_le_add crossFirst crossSecond).trans
    change 2 * scales.circulation (second.val + 1) /
        (Real.pi * (|scales.location (first.val + 1) - scales.location (second.val + 1)| / 8)) +
      2 * scales.circulation (first.val + 1) /
        (Real.pi * (|scales.location (second.val + 1) - scales.location (first.val + 1)| / 8)) ≤ _
    rw [abs_sub_comm (scales.location (second.val + 1))]
    calc
      _ = (16 / (Real.pi * |scales.location (first.val + 1) - scales.location (second.val + 1)|)) *
          (scales.circulation (first.val + 1) + scales.circulation (second.val + 1)) := by ring
      _ ≤ (16 / (Real.pi * |scales.location (first.val + 1) - scales.location (second.val + 1)|)) *
          (9 * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)| ^ 2) :=
        mul_le_mul_of_nonneg_left massBound (by positivity)
      _ = _ := by
        have cancellation (gap rate : ℝ) (nonzero : gap ≠ 0) :
            (16 / (Real.pi * gap)) * (9 * rate * gap ^ 2) = (144 / Real.pi) * rate * gap := by
          field_simp
          <;> ring
        exact cancellation _ _ gapPositive.ne'
  have firstErase := Finset.sum_erase_add (Finset.univ.erase first)
    (fun source => field source (center first)) (Finset.mem_erase.mpr ⟨Ne.symm different, Finset.mem_univ _⟩)
  have secondErase := Finset.sum_erase_add (Finset.univ.erase second)
    (fun source => field source (center second)) (Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩)
  rw [Finset.erase_right_comm] at secondErase
  rw [externalIdentity, externalIdentity, ← firstErase, ← secondErase]
  have identity : (∑ source ∈ common, field source (center first)) + field second (center first) -
      ((∑ source ∈ common, field source (center second)) + field first (center second)) =
      (∑ source ∈ common, (field source (center first) - field source (center second))) +
        (field second (center first) - field first (center second)) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add commonSumBound mutualBound)

end EulerNonuniqueness.Paper
