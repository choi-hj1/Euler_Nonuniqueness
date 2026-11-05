import EulerNonuniqueness.General.SupportedFieldCutoff

noncomputable section

open Set Metric

namespace EulerNonuniqueness.General

variable {Domain Range : Type*} [PseudoMetricSpace Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

def distanceFieldCutoff (admissible : Set Domain) (margin : ℝ) (point : Domain) : ℝ :=
  min 1 (infDist point admissibleᶜ / margin)

theorem distanceFieldCutoff_nonnegative (admissible : Set Domain) {margin : ℝ} (positive : 0 < margin)
    (point : Domain) : 0 ≤ distanceFieldCutoff admissible margin point :=
  le_min zero_le_one (div_nonneg infDist_nonneg positive.le)

theorem distanceFieldCutoff_abs_le_one (admissible : Set Domain) {margin : ℝ} (positive : 0 < margin)
    (point : Domain) : |distanceFieldCutoff admissible margin point| ≤ 1 := by
  rw [abs_of_nonneg (distanceFieldCutoff_nonnegative admissible positive point)]
  exact min_le_left _ _

theorem distanceFieldCutoff_zero_outside (admissible : Set Domain) (margin : ℝ) (point : Domain)
    (outside : point ∉ admissible) : distanceFieldCutoff admissible margin point = 0 := by
  rw [distanceFieldCutoff, infDist_zero_of_mem outside, zero_div, min_eq_right zero_le_one]

theorem distanceFieldCutoff_one (admissible : Set Domain) {margin : ℝ} (positive : 0 < margin)
    (point : Domain) (inside : margin ≤ infDist point admissibleᶜ) :
    distanceFieldCutoff admissible margin point = 1 := by
  exact min_eq_left ((le_div_iff₀ positive).mpr (by simpa only [one_mul] using inside))

theorem distanceFieldCutoff_lipschitz (admissible : Set Domain) {margin : ℝ} (positive : 0 < margin) :
    LipschitzWith ⟨margin⁻¹, inv_nonneg.mpr positive.le⟩ (distanceFieldCutoff admissible margin) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have identityLipschitz : LipschitzWith 1 (id : ℝ → ℝ) := LipschitzWith.id
  have minimum := (identityLipschitz.const_min 1).dist_le_mul
    (infDist first admissibleᶜ / margin) (infDist second admissibleᶜ / margin)
  have distance := (lipschitz_infDist_pt admissibleᶜ).dist_le_mul first second
  rw [Real.dist_eq] at distance
  change |min 1 (infDist first admissibleᶜ / margin) - min 1 (infDist second admissibleᶜ / margin)| ≤ _
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, id_eq] at minimum
  calc
    _ ≤ |infDist first admissibleᶜ / margin - infDist second admissibleᶜ / margin| := minimum
    _ = |infDist first admissibleᶜ - infDist second admissibleᶜ| / margin := by
      rw [← sub_div, abs_div, abs_of_pos positive]
    _ ≤ dist first second / margin := div_le_div_of_nonneg_right (by simpa only [NNReal.coe_one, one_mul] using distance) positive.le
    _ = _ := by simp only [NNReal.coe_mk, div_eq_mul_inv]; ring

theorem lipschitzWith_distanceFieldCutoff_smul
    (field : Domain → Range) (admissible : Set Domain) {margin : ℝ} (positive : 0 < margin)
    (fieldConstant bound : NNReal)
    (fieldLipschitz : LipschitzOnWith fieldConstant field admissible)
    (fieldBound : ∀ point ∈ admissible, ‖field point‖ ≤ bound) :
    LipschitzWith (fieldConstant + ⟨margin⁻¹, inv_nonneg.mpr positive.le⟩ * bound)
      (fun point => distanceFieldCutoff admissible margin point • field point) :=
  lipschitzWith_smul_of_supported_lipschitzOn field (distanceFieldCutoff admissible margin) admissible
    fieldConstant ⟨margin⁻¹, inv_nonneg.mpr positive.le⟩ bound
    fieldLipschitz (distanceFieldCutoff_lipschitz admissible positive)
    (distanceFieldCutoff_abs_le_one admissible positive)
    (distanceFieldCutoff_zero_outside admissible margin) fieldBound

theorem distanceFieldCutoff_smul_norm_bound
    (field : Domain → Range) (admissible : Set Domain) {margin : ℝ} (positive : 0 < margin)
    (bound : NNReal) (fieldBound : ∀ point ∈ admissible, ‖field point‖ ≤ bound) (point : Domain) :
    ‖distanceFieldCutoff admissible margin point • field point‖ ≤ bound := by
  by_cases inside : point ∈ admissible
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (distanceFieldCutoff_abs_le_one admissible positive point) (norm_nonneg _)).trans
      (by simpa only [one_mul] using fieldBound point inside)
  · rw [distanceFieldCutoff_zero_outside admissible margin point inside, zero_smul, norm_zero]
    exact bound.coe_nonneg

end EulerNonuniqueness.General
