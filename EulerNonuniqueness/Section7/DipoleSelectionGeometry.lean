import EulerNonuniqueness.Section7.ActualDipolePairDomains

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

def selectedDipolePatches {count : ℕ} (outer : Fin count) (first : Bool) : Finset (Fin count × Fin 4) :=
  if first then {(outer, 0), (outer, 3)} else {(outer, 1), (outer, 2)}

def selectedDipoleCenter {count : ℕ} (motion : PatchMotion count) (time : ℝ) (outer : Fin count) (first : Bool) : ℂ :=
  if first then firstDipoleCenter motion time outer else secondDipoleCenter motion time outer

theorem selectedDipolePatches_card {count : ℕ} (outer : Fin count) (first : Bool) :
    (selectedDipolePatches outer first).card = 2 := by cases first <;> simp [selectedDipolePatches]

theorem selectedDipolePatches_outer {count : ℕ} (outer : Fin count) (first : Bool)
    (pair : Fin count × Fin 4) (inside : pair ∈ selectedDipolePatches outer first) : pair.1 = outer := by
  cases first <;> simp only [selectedDipolePatches, Bool.false_eq_true, if_false, if_true, Finset.mem_insert,
    Finset.mem_singleton] at inside <;> rcases inside with rfl | rfl <;> rfl

theorem selectedDipolePatches_center {count : ℕ} (motion : PatchMotion count) (time : ℝ)
    (outer : Fin count) (first : Bool) (pair : Fin count × Fin 4) (inside : pair ∈ selectedDipolePatches outer first) :
    dipoleCenterForPatch motion time pair.1 pair.2 = selectedDipoleCenter motion time outer first := by
  cases first <;> simp only [selectedDipolePatches, Bool.false_eq_true, if_false, if_true, Finset.mem_insert,
    Finset.mem_singleton] at inside <;> rcases inside with rfl | rfl <;> rfl

theorem unselectedDipolePatches_center {count : ℕ} (motion : PatchMotion count) (time : ℝ)
    (outer : Fin count) (first : Bool) (patch : Fin 4) (outside : (outer, patch) ∉ selectedDipolePatches outer first) :
    dipoleCenterForPatch motion time outer patch = selectedDipoleCenter motion time outer (!first) := by
  cases first <;> by_cases zero : patch = 0 <;> by_cases three : patch = 3 <;>
    simp_all [dipoleCenterForPatch, selectedDipoleCenter, selectedDipolePatches]
  all_goals omega

theorem selectedDipoleCenter_gap {count : ℕ} (motion : PatchMotion count) (time : ℝ) (outer : Fin count) (first : Bool) :
    ‖selectedDipoleCenter motion time outer first - selectedDipoleCenter motion time outer (!first)‖ =
      ‖firstDipoleCenter motion time outer - secondDipoleCenter motion time outer‖ := by
  cases first <;> simp [selectedDipoleCenter, norm_sub_rev]

theorem selectedDipoleCenter_near_quadcenter {count : ℕ} (motion : PatchMotion count) (time : ℝ)
    (outer : Fin count) (first : Bool) {radius : ℝ}
    (near : ∀ patch, ‖patchCentroid motion time outer patch - quadrupoleCenter motion time outer‖ ≤ radius) :
    ‖selectedDipoleCenter motion time outer first - quadrupoleCenter motion time outer‖ ≤ radius := by
  have average (first second center : ℂ) : ‖(first + second) / 2 - center‖ ≤ (‖first - center‖ + ‖second - center‖) / 2 := by
    rw [show (first + second) / 2 - center = ((first - center) + (second - center)) / 2 by ring, norm_div]
    norm_num
    linarith [norm_add_le (first - center) (second - center)]
  cases first <;> simp only [selectedDipoleCenter, Bool.false_eq_true, if_false, if_true, firstDipoleCenter, secondDipoleCenter]
  · exact (average _ _ _).trans (by linarith [near 1, near 2])
  · exact (average _ _ _).trans (by linarith [near 0, near 3])

theorem exists_selectedDipoleCenter_far {count : ℕ} (motion : PatchMotion count) (time : ℝ)
    (outer : Fin count) (center : ℂ) :
    ∃ first : Bool, ‖firstDipoleCenter motion time outer - secondDipoleCenter motion time outer‖ / 2 ≤
      ‖selectedDipoleCenter motion time outer first - center‖ := by
  by_cases far : ‖firstDipoleCenter motion time outer - secondDipoleCenter motion time outer‖ / 2 ≤
      ‖firstDipoleCenter motion time outer - center‖
  · exact ⟨true, far⟩
  · refine ⟨false, ?_⟩
    have triangle := norm_sub_le_norm_sub_add_norm_sub (firstDipoleCenter motion time outer) center
      (secondDipoleCenter motion time outer)
    rw [norm_sub_rev center] at triangle
    change _ ≤ ‖secondDipoleCenter motion time outer - center‖
    linarith

theorem domain_far_of_block_center_separation {position center outerCenter otherCenter : ℂ} {scale : ℝ}
    (separated : scale / 4 ≤ ‖outerCenter - otherCenter‖)
    (centerNear : ‖center - outerCenter‖ ≤ scale / 16)
    (positionNear : ‖position - otherCenter‖ ≤ scale / 50) :
    scale / 8 ≤ ‖position - center‖ := by
  have first := norm_sub_le_norm_sub_add_norm_sub outerCenter center otherCenter
  have second := norm_sub_le_norm_sub_add_norm_sub center position otherCenter
  rw [norm_sub_rev outerCenter center] at first
  rw [norm_sub_rev center position] at second
  linarith [norm_nonneg (center - outerCenter)]

end EulerNonuniqueness.Paper
