import Mathlib

noncomputable section

open Set

theorem ContinuousOn.continuousOn_sSup_image_Icc
    {function : ℝ → ℝ} {lower upper : ℝ} (ordered : lower ≤ upper)
    (regular : ContinuousOn function (Icc lower upper)) :
    ContinuousOn (fun time => sSup (function '' Icc lower time)) (Icc lower upper) := by
  let extended := fun time => function (projIcc lower upper ordered time)
  have extendedContinuous : Continuous extended :=
    (continuousOn_iff_continuous_restrict.mp regular).comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc lower upper) : extended time = function time := by
    simp only [extended, projIcc_of_mem ordered inside]
  let sampled := fun time parameter : ℝ => extended (lower + (time - lower) * parameter)
  have sampledContinuous : Continuous (fun pair : ℝ × ℝ => sampled pair.1 pair.2) := by
    dsimp only [sampled]
    exact extendedContinuous.comp (continuous_const.add ((continuous_fst.sub continuous_const).mul continuous_snd))
  have maximumContinuous : Continuous (fun time => sSup (sampled time '' Icc (0 : ℝ) 1)) :=
    isCompact_Icc.continuous_sSup sampledContinuous
  have imageIdentity (time : ℝ) (inside : time ∈ Icc lower upper) :
      sampled time '' Icc (0 : ℝ) 1 = function '' Icc lower time := by
    ext value
    constructor
    · rintro ⟨parameter, member, rfl⟩
      have pointInside : lower + (time - lower) * parameter ∈ Icc lower time := by
        constructor
        · nlinarith only [mul_nonneg (sub_nonneg.mpr inside.1) member.1]
        · nlinarith only [mul_nonneg (sub_nonneg.mpr inside.1) (sub_nonneg.mpr member.2)]
      refine ⟨lower + (time - lower) * parameter, pointInside, ?_⟩
      exact (agreement _ ⟨pointInside.1, pointInside.2.trans inside.2⟩).symm
    · rintro ⟨point, member, rfl⟩
      by_cases same : time = lower
      · have pointSame : point = lower := by linarith only [member.1, member.2, same]
        refine ⟨0, by norm_num, ?_⟩
        simpa only [sampled, mul_zero, add_zero, pointSame] using agreement lower ⟨le_rfl, ordered⟩
      · have positive : 0 < time - lower := sub_pos.mpr (lt_of_le_of_ne inside.1 (Ne.symm same))
        refine ⟨(point - lower) / (time - lower), ?_, ?_⟩
        · exact ⟨div_nonneg (sub_nonneg.mpr member.1) positive.le,
            (div_le_one positive).mpr (by linarith only [member.2])⟩
        · have pointIdentity : lower + (time - lower) * ((point - lower) / (time - lower)) = point := by
            field_simp
          dsimp only [sampled]
          rw [pointIdentity]
          exact agreement point ⟨member.1, member.2.trans inside.2⟩
  exact maximumContinuous.continuousOn.congr (fun time inside => congrArg sSup (imageIdentity time inside).symm)

theorem ContinuousOn.exists_exponential_running_majorant
    {function : ℝ → ℝ} {horizon rate : ℝ} (horizonNonnegative : 0 ≤ horizon)
    (regular : ContinuousOn function (Icc 0 horizon))
    (nonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ function time) :
    ∃ majorant : ℝ → ℝ, ContinuousOn majorant (Icc 0 horizon) ∧
      (∀ time ∈ Icc 0 horizon, 0 ≤ majorant time ∧ function time ≤ majorant time) ∧
      (∀ earlier ∈ Icc 0 horizon, ∀ later ∈ Icc 0 horizon, earlier ≤ later →
        majorant earlier ≤ Real.exp (-rate * (later - earlier)) * majorant later) ∧
      ∀ time ∈ Icc 0 horizon, ∃ current ∈ Icc 0 time,
        majorant time = Real.exp (rate * (time - current)) * function current := by
  let weighted := fun time => Real.exp (-rate * time) * function time
  let running := fun time => sSup (weighted '' Icc 0 time)
  let majorant := fun time => Real.exp (rate * time) * running time
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-rate * time)) := by fun_prop
  have weightedContinuous : ContinuousOn weighted (Icc 0 horizon) := exponentialContinuous.continuousOn.mul regular
  have runningContinuous : ContinuousOn running (Icc 0 horizon) :=
    weightedContinuous.continuousOn_sSup_image_Icc horizonNonnegative
  have majorantContinuous : ContinuousOn majorant (Icc 0 horizon) := by
    exact (by fun_prop : Continuous (fun time : ℝ => Real.exp (rate * time))).continuousOn.mul runningContinuous
  have bounded (time : ℝ) (inside : time ∈ Icc 0 horizon) : BddAbove (weighted '' Icc 0 time) :=
    (isCompact_Icc.image_of_continuousOn (weightedContinuous.mono (Icc_subset_Icc le_rfl inside.2))).bddAbove
  have nonempty (time : ℝ) (inside : time ∈ Icc 0 horizon) : (weighted '' Icc 0 time).Nonempty :=
    ⟨weighted 0, mem_image_of_mem weighted ⟨le_rfl, inside.1⟩⟩
  have cancellation (time : ℝ) : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [neg_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  refine ⟨majorant, majorantContinuous, ?_, ?_, ?_⟩
  · intro time inside
    have atTime : weighted time ≤ running time :=
      le_csSup (bounded time inside) (mem_image_of_mem weighted ⟨inside.1, le_rfl⟩)
    have atZero : weighted 0 ≤ running time :=
      le_csSup (bounded time inside) (mem_image_of_mem weighted ⟨le_rfl, inside.1⟩)
    have weightedZero : 0 ≤ weighted 0 := mul_nonneg (Real.exp_pos _).le (nonnegative 0 ⟨le_rfl, horizonNonnegative⟩)
    have actual := mul_le_mul_of_nonneg_left atTime (Real.exp_pos (rate * time)).le
    change Real.exp (rate * time) * (Real.exp (-rate * time) * function time) ≤ majorant time at actual
    rw [← mul_assoc, cancellation, one_mul] at actual
    exact ⟨mul_nonneg (Real.exp_pos _).le (weightedZero.trans atZero), actual⟩
  · intro earlier earlierInside later laterInside ordered
    have runningBound : running earlier ≤ running later := by
      apply csSup_le (nonempty earlier earlierInside)
      rintro value ⟨current, member, rfl⟩
      exact le_csSup (bounded later laterInside) (mem_image_of_mem weighted ⟨member.1, member.2.trans ordered⟩)
    have actual := mul_le_mul_of_nonneg_left runningBound (Real.exp_pos (rate * earlier)).le
    apply actual.trans_eq
    dsimp only [majorant]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · intro time inside
    have attained := (isCompact_Icc.image_of_continuousOn
      (weightedContinuous.mono (Icc_subset_Icc le_rfl inside.2))).sSup_mem (nonempty time inside)
    obtain ⟨current, member, maximum⟩ := attained
    refine ⟨current, member, ?_⟩
    change Real.exp (rate * time) * sSup (weighted '' Icc 0 time) = _
    rw [← maximum]
    dsimp only [weighted]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
