import EulerNonuniqueness.Section5.CascadeStatement
import EulerNonuniqueness.Section4.ReferenceCutoffSlack

noncomputable section

namespace EulerNonuniqueness.Paper

def cascadeInitialCenter {count : ℕ} (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (phase unstable : Fin count → ℝ) (dipoleAngle : ℝ)
    (label : Fin count × Fin 4) : ℂ :=
  if label.1.val + 1 = count then
    separatingInitialCenter scales orbit sectionTime dipoleAngle count label.2
  else initialDiskCenter scales (label.1.val + 1) (phase label.1) (unstable label.1) label.2

theorem separatingInitialCenter_offset_bound (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime dipoleAngle : ℝ) (index : ℕ) (patch : Fin 4) :
    ‖separatingInitialCenter scales orbit sectionTime dipoleAngle index patch -
      (scales.location index : ℂ)‖ ≤
        scales.length index * max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖ := by
  have rotation : ‖Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  simp only [separatingInitialCenter, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (scales.length_pos index), rotation, mul_one]
  apply mul_le_mul_of_nonneg_left _ (scales.length_pos index).le
  split_ifs <;> first
    | exact le_max_left _ _
    | exact le_max_right _ _
    | simpa only [norm_neg] using (le_max_left ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
    | simpa only [norm_neg] using (le_max_right ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)

theorem separatingInitialCenter_pair_lower (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime dipoleAngle minimum : ℝ)
    (positiveGap : minimum ≤ 2 * ‖orbit.positive sectionTime‖)
    (negativeGap : minimum ≤ 2 * ‖orbit.negative sectionTime‖)
    (differenceGap : minimum ≤ ‖orbit.positive sectionTime - orbit.negative sectionTime‖)
    (sumGap : minimum ≤ ‖orbit.positive sectionTime + orbit.negative sectionTime‖)
    (index : ℕ) (first second : Fin 4) (different : first ≠ second) :
    scales.length index * minimum ≤
      ‖separatingInitialCenter scales orbit sectionTime dipoleAngle index first -
        separatingInitialCenter scales orbit sectionTime dipoleAngle index second‖ := by
  have rotation : ‖Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have normIdentity (firstPoint secondPoint : ℂ) :
      ‖((scales.location index : ℂ) + (scales.length index : ℂ) *
          Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ)) * firstPoint) -
        ((scales.location index : ℂ) + (scales.length index : ℂ) *
          Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ)) * secondPoint)‖ =
        scales.length index * ‖firstPoint - secondPoint‖ := by
    rw [show ((scales.location index : ℂ) + (scales.length index : ℂ) *
        Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ)) * firstPoint) -
        ((scales.location index : ℂ) + (scales.length index : ℂ) *
        Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ)) * secondPoint) =
        (scales.length index : ℂ) *
        Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ)) *
        (firstPoint - secondPoint) by ring]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (scales.length_pos index), rotation, mul_one]
  unfold separatingInitialCenter
  rw [normIdentity]
  apply mul_le_mul_of_nonneg_left _ (scales.length_pos index).le
  have opposite (point : ℂ) : ‖point - -point‖ = 2 * ‖point‖ := by
    rw [show point - -point = (2 : ℝ) • point by simp [two_smul]]
    simp [norm_smul]
  have positiveOpposite : minimum ≤ ‖orbit.positive sectionTime - -orbit.positive sectionTime‖ := by
    rw [opposite]
    exact positiveGap
  have negativeOpposite : minimum ≤ ‖orbit.negative sectionTime - -orbit.negative sectionTime‖ := by
    rw [opposite]
    exact negativeGap
  fin_cases first <;> fin_cases second <;>
    simp_all [sub_neg_eq_add, neg_sub, norm_neg, norm_sub_rev, add_comm]
  · rw [show -orbit.positive sectionTime - orbit.negative sectionTime =
      -(orbit.positive sectionTime + orbit.negative sectionTime) by abel, norm_neg]
    exact sumGap
  · rw [show -orbit.positive sectionTime + orbit.negative sectionTime =
      -(orbit.positive sectionTime - orbit.negative sectionTime) by abel, norm_neg]
    exact differenceGap
  · simpa only [sub_eq_add_neg] using differenceGap

theorem cascadeInitialCenter_offset_bound {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (phase unstable : Fin count → ℝ)
    (dipoleAngle bound : ℝ) (referenceSmall : ∀ index, |unstable index| ≤ 1 / 2)
    (referenceBound : 3 ≤ bound)
    (positiveBound : ‖orbit.positive sectionTime‖ ≤ bound)
    (negativeBound : ‖orbit.negative sectionTime‖ ≤ bound)
    (label : Fin count × Fin 4) :
    ‖cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle label -
      (scales.location (label.1.val + 1) : ℂ)‖ ≤ bound * scales.length (label.1.val + 1) := by
  unfold cascadeInitialCenter
  split_ifs with last
  · have estimate := separatingInitialCenter_offset_bound scales orbit sectionTime dipoleAngle
      (label.1.val + 1) label.2
    have boundEstimate : scales.length (label.1.val + 1) *
        max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖ ≤
        bound * scales.length (label.1.val + 1) := by
      nlinarith [max_le positiveBound negativeBound, scales.length_pos (label.1.val + 1)]
    simpa only [last] using estimate.trans boundEstimate
  · have estimate := initialDiskCenter_offset_bound scales (label.1.val + 1)
      (phase label.1) (unstable label.1) (referenceSmall label.1) label.2
    nlinarith [scales.length_pos (label.1.val + 1)]

theorem separated_scaled_centers_of_offset_and_internal_gap {count : ℕ}
    (scales : Scales) (centers : Fin count × Fin 4 → ℂ) (minimum : ℝ)
    (minimumPositive : 0 < minimum)
    (offset : ∀ label, ‖centers label - (scales.location (label.1.val + 1) : ℂ)‖ ≤
      scales.location (label.1.val + 1) / 100)
    (internal : ∀ index first second, first ≠ second →
      minimum * scales.length (index.val + 1) ≤ ‖centers (index, first) - centers (index, second)‖)
    (radiusInternal : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ minimum * scales.length (index.val + 1) / 12)
    (radiusLocation : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 100) :
    ∀ first second, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) <
        ‖centers first - centers second‖ := by
  rintro ⟨firstIndex, firstPatch⟩ ⟨secondIndex, secondPatch⟩ different
  by_cases same : firstIndex = secondIndex
  · subst secondIndex
    have patchDifferent : firstPatch ≠ secondPatch := fun equality => different (Prod.ext rfl equality)
    have estimate := internal firstIndex firstPatch secondPatch patchDifferent
    have positive := mul_pos minimumPositive (scales.length_pos (firstIndex.val + 1))
    linarith [radiusInternal firstIndex]
  · have locations := scales.location_sum_le_three_distance
      (show firstIndex.val + 1 ≠ secondIndex.val + 1 from
        fun equality => same (Fin.ext (Nat.add_right_cancel equality)))
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (scales.location (firstIndex.val + 1) : ℂ) (centers (firstIndex, firstPatch))
      (scales.location (secondIndex.val + 1) : ℂ)
    have last := norm_sub_le_norm_sub_add_norm_sub (centers (firstIndex, firstPatch))
      (centers (secondIndex, secondPatch)) (scales.location (secondIndex.val + 1) : ℂ)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      norm_sub_rev (scales.location (firstIndex.val + 1) : ℂ)] at triangle
    have positive := scales.location_distance_pos
      (show firstIndex.val + 1 ≠ secondIndex.val + 1 from
        fun equality => same (Fin.ext (Nat.add_right_cancel equality)))
    linarith [offset (firstIndex, firstPatch), offset (secondIndex, secondPatch),
      radiusLocation firstIndex, radiusLocation secondIndex]

theorem cascadeInitialCenter_separated {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (phase unstable : Fin count → ℝ)
    (dipoleAngle minimum bound : ℝ) (minimumPositive : 0 < minimum) (minimumSmall : minimum ≤ 1 / 4)
    (referenceSmall : ∀ index, |unstable index| ≤ 1 / 2)
    (referenceBound : 3 ≤ bound)
    (positiveBound : ‖orbit.positive sectionTime‖ ≤ bound)
    (negativeBound : ‖orbit.negative sectionTime‖ ≤ bound)
    (positiveGap : minimum ≤ 2 * ‖orbit.positive sectionTime‖)
    (negativeGap : minimum ≤ 2 * ‖orbit.negative sectionTime‖)
    (differenceGap : minimum ≤ ‖orbit.positive sectionTime - orbit.negative sectionTime‖)
    (sumGap : minimum ≤ ‖orbit.positive sectionTime + orbit.negative sectionTime‖)
    (lengthSmall : ∀ index : Fin count,
      bound * scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ minimum * scales.length (index.val + 1) / 12) :
    ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) <
        ‖cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle first -
          cascadeInitialCenter scales orbit sectionTime phase unstable dipoleAngle second‖ := by
  apply separated_scaled_centers_of_offset_and_internal_gap scales _ minimum minimumPositive
  · intro label
    exact (cascadeInitialCenter_offset_bound scales orbit sectionTime phase unstable dipoleAngle bound
      referenceSmall referenceBound positiveBound negativeBound label).trans (lengthSmall label.1)
  · intro index first second different
    unfold cascadeInitialCenter
    simp only [Prod.fst, Prod.snd]
    split_ifs with last
    · simpa only [last, mul_comm] using separatingInitialCenter_pair_lower scales orbit sectionTime dipoleAngle
        minimum positiveGap negativeGap differenceGap sumGap (index.val + 1) first second different
    · have estimate := initialDiskCenter_same_scale_separation scales (index.val + 1)
        (phase index) (unstable index) (referenceSmall index) first second different
      nlinarith [scales.length_pos (index.val + 1)]
  · exact radiusSmall
  · intro index
    nlinarith [radiusSmall index, lengthSmall index, scales.length_pos (index.val + 1)]

theorem IsNormalizedSeparatingOrbit.exists_cascade_initial_geometry
    {orbit : SeparatingOrbit} (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime : ℝ) :
    ∃ minimum bound : ℝ, 0 < minimum ∧ minimum ≤ 1 / 4 ∧ 3 ≤ bound ∧
      ‖orbit.positive sectionTime‖ ≤ bound ∧ ‖orbit.negative sectionTime‖ ≤ bound ∧
      minimum ≤ 2 * ‖orbit.positive sectionTime‖ ∧
      minimum ≤ 2 * ‖orbit.negative sectionTime‖ ∧
      minimum ≤ ‖orbit.positive sectionTime - orbit.negative sectionTime‖ ∧
      minimum ≤ ‖orbit.positive sectionTime + orbit.negative sectionTime‖ := by
  obtain ⟨distance, distancePositive, distanceBound⟩ := normalized.2.2.1
  refine ⟨min distance (1 / 4), max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖),
    lt_min distancePositive (by norm_num), min_le_right _ _, le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _), ?_⟩
  exact ⟨(min_le_left _ _).trans (distanceBound sectionTime).1,
    (min_le_left _ _).trans (distanceBound sectionTime).2.1,
    (min_le_left _ _).trans (distanceBound sectionTime).2.2.1,
    (min_le_left _ _).trans (distanceBound sectionTime).2.2.2⟩

end EulerNonuniqueness.Paper
