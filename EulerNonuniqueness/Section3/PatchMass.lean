import EulerNonuniqueness.Section1.Scales

open MeasureTheory Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem patchDensity_integrable {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4)
    (domain_open : IsOpen (motion.domain time index patch))
    (domain_bounded : Bornology.IsBounded (motion.domain time index patch)) :
    Integrable (patchDensity scales motion time index patch) := by
  apply (integrable_indicator_iff domain_open.measurableSet).2
  exact integrableOn_const.2 (Or.inr domain_bounded.measure_lt_top)

theorem patchDensity_integral {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4)
    (domain_open : IsOpen (motion.domain time index patch))
    (domain_area : volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitude_pos : 0 < scales.amplitude) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) :
    (∫ position, patchDensity scales motion time index patch position) =
      patchSign patch * scales.circulation (index.val + 1) := by
  rw [patchDensity, integral_indicator_const _ domain_open.measurableSet]
  change (volume (motion.domain time index patch)).toReal *
    (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) = _
  rw [domain_area, ENNReal.toReal_ofReal (by positivity)]
  have circulation := scales.patch_circulation amplitude_pos frequency_pos ratio_pos
    (index.val + 1)
  calc
    _ = patchSign patch * (Real.pi * scales.radius (index.val + 1) ^ 2 *
        scales.amplitude * scales.omega (index.val + 1) ^ 4) := by ring
    _ = _ := by rw [circulation]

theorem quadrupoleDensity_integral_zero {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (domain_open : ∀ patch, IsOpen (motion.domain time index patch))
    (domain_bounded : ∀ patch, Bornology.IsBounded (motion.domain time index patch))
    (domain_area : ∀ patch, volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitude_pos : 0 < scales.amplitude) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) :
    (∫ position, quadrupoleDensity scales motion time index position) = 0 := by
  unfold quadrupoleDensity
  rw [integral_finset_sum _ (fun patch _ => patchDensity_integrable scales motion time
    index patch (domain_open patch) (domain_bounded patch))]
  simp_rw [patchDensity_integral scales motion time index _ (domain_open _)
    (domain_area _) amplitude_pos frequency_pos ratio_pos]
  norm_num [Fin.sum_univ_succ, patchSign]

theorem FinitePatchEvolution.patch_mass {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (amplitude_pos : 0 < scales.amplitude) (frequency_pos : 0 < scales.frequency)
    (ratio_pos : 0 < scales.ratio) (time : ℝ) (time_mem : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) :
    Integrable (patchDensity scales motion time index patch) ∧
      (∫ position, patchDensity scales motion time index patch position) =
        patchSign patch * scales.circulation (index.val + 1) := by
  obtain ⟨domain_open, domain_bounded, domain_area, _⟩ :=
    evolution.2.2.2.1 time time_mem index patch
  exact ⟨patchDensity_integrable scales motion time index patch domain_open domain_bounded,
    patchDensity_integral scales motion time index patch domain_open domain_area
      amplitude_pos frequency_pos ratio_pos⟩

end EulerNonuniqueness.Paper
