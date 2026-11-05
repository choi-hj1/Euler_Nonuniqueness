import EulerNonuniqueness.Section6.PaperExternalStaticData
import EulerNonuniqueness.Section6.FiniteExteriorWeightBound
import EulerNonuniqueness.Section1.CirculationPairStrain
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem FinitePatchEvolution.external_inverseSquare_weight_le_strain
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) (center : ℂ)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain time source patch →
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤ ‖center - position‖) :
    (∫ position, inverseSquareVorticityWeight (externalPatchVorticity scales motion time index) center position) ≤
      2304 * scales.strain := by
  classical
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  let distance := fun source : Fin count =>
    |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < distance source := by
    apply div_pos _ (by norm_num)
    apply scales.location_distance_pos
    intro equal
    exact (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equal).symm)
  have quadSeparated (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      ∀ position ∈ Function.support (quadrupoleDensity scales motion time source),
        distance source ≤ ‖center - position‖ := by
    intro position nonzero
    by_contra outside
    have vanishes (patch : Fin 4) : patchDensity scales motion time source patch position = 0 := by
      apply indicator_of_not_mem
      exact fun inDomain => outside (separated source member patch position inDomain)
    exact nonzero (by simp only [quadrupoleDensity, vanishes, Finset.sum_const_zero])
  have componentIntegrable (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      Integrable (inverseSquareVorticityWeight (quadrupoleDensity scales motion time source) center) :=
    integrable_inverseSquareVorticityWeight (evolution.quadrupoleDensity_integrable inside source)
      center (positive source member) (quadSeparated source member)
  have globalPositive : 0 < scales.location (index.val + 1) / 24 := by
    exact div_pos (scales.location_pos _) (by norm_num)
  have globalSeparation : ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain time source patch →
        scales.location (index.val + 1) / 24 ≤ ‖center - position‖ := by
    intro source member patch position inDomain
    have different := (Finset.mem_erase.mp member).1
    have locations := scales.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equal => different (Fin.ext (Nat.add_right_cancel equal).symm))
    have sourcePositive := scales.location_pos (source.val + 1)
    have lower : scales.location (index.val + 1) / 24 ≤ distance source := by
      dsimp only [distance]
      linarith only [locations, sourcePositive]
    exact lower.trans (separated source member patch position inDomain)
  have totalIntegrable := integrable_inverseSquareVorticityWeight
    (evolution.externalPatchVorticity_integrable inside index) center globalPositive
    (externalPatchVorticity_support_separated scales motion time index center _ globalSeparation)
  have pointwise (position : ℂ) :
      inverseSquareVorticityWeight (externalPatchVorticity scales motion time index) center position ≤
        ∑ source ∈ Finset.univ.erase index,
          inverseSquareVorticityWeight (quadrupoleDensity scales motion time source) center position := by
    have triangle : |externalPatchVorticity scales motion time index position| ≤
        ∑ source ∈ Finset.univ.erase index, |quadrupoleDensity scales motion time source position| := by
      simpa only [externalPatchVorticity, Real.norm_eq_abs] using norm_sum_le
        (Finset.univ.erase index) (fun source => quadrupoleDensity scales motion time source position)
    unfold inverseSquareVorticityWeight
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right triangle (sq_nonneg _)
  have comparison := integral_mono totalIntegrable
    (integrable_finset_sum _ componentIntegrable) pointwise
  rw [integral_finset_sum _ componentIntegrable] at comparison
  have massComparison :
      (∑ source ∈ Finset.univ.erase index,
        ∫ position, inverseSquareVorticityWeight (quadrupoleDensity scales motion time source) center position) ≤
      4 * ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source member
    have estimate := integral_inverseSquareVorticityWeight_le_mass
      (evolution.quadrupoleDensity_integrable inside source) center (positive source member) (quadSeparated source member)
    have mass := evolution.quadrupoleDensity_integral_abs_le inside amplitudePositive frequencyPositive ratioPositive source
    have scaled := mul_le_mul_of_nonneg_left mass (sq_nonneg ((distance source)⁻¹))
    exact estimate.trans (scaled.trans_eq (by simp only [div_eq_mul_inv, inv_pow]; ring))
  have finiteBound := mul_le_mul_of_nonneg_left
    (scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive index 2) (by norm_num : (0 : ℝ) ≤ 4)
  apply comparison.trans (massComparison.trans _)
  exact finiteBound.trans_eq (by unfold Scales.strain; norm_num; ring)

end EulerNonuniqueness.Paper
