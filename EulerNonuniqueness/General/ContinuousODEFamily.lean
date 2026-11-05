import EulerNonuniqueness.General.BoundedLipschitzODE
import Mathlib.Analysis.ODE.Gronwall

noncomputable section

open Set Metric Filter
open scoped NNReal Topology

theorem exists_jointly_continuous_family_of_bounded_lipschitz_ODE
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [CompleteSpace space]
    {field : space → space} {lipschitzBound speedBound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound field) (bounded : ∀ state, ‖field state‖ ≤ speedBound)
    {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon) :
    ∃ flow : space → ℝ → space,
      (∀ initial, flow initial 0 = initial) ∧
      Continuous (fun point : space × ℝ => flow point.1 point.2) ∧
      (∀ initial time, time ∈ Ioo 0 horizon → HasDerivAt (flow initial) (field (flow initial time)) time) ∧
      ∀ first second time, dist (flow first time) (flow second time) ≤
        dist first second * Real.exp ((lipschitzBound : ℝ) * horizon) := by
  classical
  choose paths initialEquality pathsContinuous derivatives displacementBound using
    (fun initial : space => exists_solution_Icc_of_bounded_lipschitz lipschitz bounded initial horizonNonnegative)
  have rightDerivative (initial : space) (time : ℝ) (inside : time ∈ Ico 0 horizon) :
      HasDerivWithinAt (paths initial) (field (paths initial time)) (Ici time) time :=
    (derivatives initial time ⟨inside.1, inside.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem inside)
  have labelEstimate (first second : space) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      dist (paths first time) (paths second time) ≤
        dist first second * Real.exp ((lipschitzBound : ℝ) * horizon) := by
    have estimate := dist_le_of_trajectories_ODE (v := fun _ => field) (fun _ => lipschitz)
      (pathsContinuous first) (rightDerivative first) (pathsContinuous second) (rightDerivative second)
      (δ := dist first second) (by rw [initialEquality, initialEquality]) time inside
    apply estimate.trans
    apply mul_le_mul_of_nonneg_left _ dist_nonneg
    apply Real.exp_le_exp.mpr
    simpa only [sub_zero] using mul_le_mul_of_nonneg_left inside.2 lipschitzBound.coe_nonneg
  let labelBound : ℝ≥0 := ⟨Real.exp ((lipschitzBound : ℝ) * horizon), (Real.exp_pos _).le⟩
  have labelLipschitz (time : Icc (0 : ℝ) horizon) : LipschitzWith labelBound (fun initial => paths initial time) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [labelBound, NNReal.coe_mk, mul_comm] using labelEstimate first second time time.property
  have timeLipschitz (initial : space) : LipschitzWith speedBound (fun time : Icc (0 : ℝ) horizon => paths initial time) := by
    have localBound : LipschitzOnWith speedBound (paths initial) (Icc 0 horizon) :=
      (convex_Icc 0 horizon).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (derivatives initial)
        (fun time _ => by exact_mod_cast bounded (paths initial time))
    intro first second
    exact localBound first.property second.property
  have restrictedJointContinuous : Continuous (fun point : space × Icc (0 : ℝ) horizon => paths point.1 point.2) :=
    (LipschitzWith.uncurry labelLipschitz timeLipschitz).continuous
  let projection : ℝ → Icc (0 : ℝ) horizon := projIcc 0 horizon horizonNonnegative
  have projectionContinuous : Continuous projection := continuous_projIcc
  let flow : space → ℝ → space := fun initial time => paths initial (projection time)
  have projectionIdentity (time : ℝ) (inside : time ∈ Icc 0 horizon) : (projection time : ℝ) = time :=
    congrArg Subtype.val (projIcc_of_mem horizonNonnegative inside)
  have flowInitial (initial : space) : flow initial 0 = initial := by
    dsimp only [flow]
    rw [projectionIdentity 0 ⟨le_rfl, horizonNonnegative⟩, initialEquality]
  refine ⟨flow, flowInitial, restrictedJointContinuous.comp
    (continuous_fst.prodMk (projectionContinuous.comp continuous_snd)), ?_, ?_⟩
  · intro initial time inside
    have agrees : flow initial =ᶠ[𝓝 time] paths initial := by
      filter_upwards [Icc_mem_nhds inside.1 inside.2] with current currentInside
      dsimp only [flow]
      rw [projectionIdentity current currentInside]
    have pointEquality := agrees.eq_of_nhds
    rw [pointEquality]
    exact ((derivatives initial time ⟨inside.1.le, inside.2.le⟩).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2)).congr_of_eventuallyEq agrees
  · intro first second time
    exact labelEstimate first second (projection time) (projection time).property
