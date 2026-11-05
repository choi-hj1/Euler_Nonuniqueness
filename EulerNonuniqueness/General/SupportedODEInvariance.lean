import EulerNonuniqueness.General.CutoffODEFamily

noncomputable section

open Set Metric

namespace EulerNonuniqueness.General

theorem trajectory_mem_of_lipschitz_field_zero_outside
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    {field : Space → Space} {constant : NNReal} (lipschitz : LipschitzWith constant field)
    (admissible : Set Space) (zeroOutside : ∀ state ∉ admissible, field state = 0)
    {trajectory : ℝ → Space} {horizon : ℝ}
    (continuous : ContinuousOn trajectory (Icc 0 horizon))
    (equation : ∀ time ∈ Icc 0 horizon, HasDerivWithinAt trajectory (field (trajectory time)) (Icc 0 horizon) time)
    (initialInside : trajectory 0 ∈ admissible) :
    ∀ time ∈ Icc 0 horizon, trajectory time ∈ admissible := by
  intro time inside
  by_contra outside
  have stationary : field (trajectory time) = 0 := zeroOutside (trajectory time) outside
  have initialEquality : trajectory 0 = trajectory time := by
    have unique : EqOn trajectory (fun _ => trajectory time) (Icc 0 time) := by
      apply ODE_solution_unique_of_mem_Icc_left (v := fun _ => field) (s := fun _ => univ)
        (K := constant) (fun _ _ => lipschitz.lipschitzOnWith)
        (continuous.mono (Icc_subset_Icc le_rfl inside.2))
      · intro current currentInside
        exact (equation current ⟨currentInside.1.le, currentInside.2.trans inside.2⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨currentInside.1, currentInside.2.trans inside.2⟩)
      · intro _ _
        trivial
      · exact continuousOn_const
      · intro current _currentInside
        rw [stationary]
        exact hasDerivWithinAt_const (𝕜 := ℝ) (x := current) (c := trajectory time) (s := Iic current)
      · intro _ _
        trivial
      · rfl
    exact unique ⟨le_rfl, inside.1⟩
  exact outside (initialEquality ▸ initialInside)

theorem trajectory_mem_of_distance_cutoff_equation
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (field : Space → Space) (admissible : Set Space) {margin : ℝ} (positive : 0 < margin)
    (fieldConstant bound : NNReal)
    (fieldLipschitz : LipschitzOnWith fieldConstant field admissible)
    (fieldBound : ∀ state ∈ admissible, ‖field state‖ ≤ bound)
    {trajectory : ℝ → Space} {horizon : ℝ}
    (continuous : ContinuousOn trajectory (Icc 0 horizon))
    (equation : ∀ time ∈ Icc 0 horizon, HasDerivWithinAt trajectory
      (distanceFieldCutoff admissible margin (trajectory time) • field (trajectory time)) (Icc 0 horizon) time)
    (initialInside : trajectory 0 ∈ admissible) :
    ∀ time ∈ Icc 0 horizon, trajectory time ∈ admissible := by
  apply trajectory_mem_of_lipschitz_field_zero_outside
    (lipschitzWith_distanceFieldCutoff_smul field admissible positive fieldConstant bound fieldLipschitz fieldBound)
    admissible _ continuous equation initialInside
  intro state outside
  rw [distanceFieldCutoff_zero_outside admissible margin state outside, zero_smul]

end EulerNonuniqueness.General
