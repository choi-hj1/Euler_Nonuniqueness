import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_biotSavart_bounds_from_material_geometry
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    {first second : ℂ} {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : ∀ patch source, source ∈ motion.domain time index patch → distance ≤ ‖first - source‖)
    (secondSeparated : ∀ patch source, source ∈ motion.domain time index patch → distance ≤ ‖second - source‖) :
    ‖biotSavart (quadrupoleDensity scales motion time index) first‖ ≤
        2 * scales.circulation (index.val + 1) / (Real.pi * distance) ∧
      ‖biotSavart (quadrupoleDensity scales motion time index) first -
          biotSavart (quadrupoleDensity scales motion time index) second‖ ≤
        (2 * scales.circulation (index.val + 1) / (Real.pi * distance ^ 2)) * ‖first - second‖ := by
  have individual (patch : Fin 4) := evolution.patch_biotSavart_bounds inside amplitudePositive
    frequencyPositive ratioPositive index patch positive (firstSeparated patch) (secondSeparated patch)
  rw [evolution.quadrupole_biotSavart_eq_sum_patch inside index first,
    evolution.quadrupole_biotSavart_eq_sum_patch inside index second]
  constructor
  · exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => (individual patch).1)).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring))
  · rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => (individual patch).2)).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring))

end EulerNonuniqueness.Paper
