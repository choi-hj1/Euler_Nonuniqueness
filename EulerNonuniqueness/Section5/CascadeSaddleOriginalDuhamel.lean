import EulerNonuniqueness.Section5.CascadePairedChartRegularity
import EulerNonuniqueness.Section5.CascadeClosedSaddleDynamics
import EulerNonuniqueness.Section5.CascadeSaddleLeadingStrainEquation
import EulerNonuniqueness.Section6.UnstableDuhamel
import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_saddle_original_duhamel
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ side, ∀ time ∈ Icc 0 finish,
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < radius) →
    let relative := fun time => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
      referenceStraightenedShape prepared.reference graph coordinate index time
    let input := fun time => quadrupoleRelativeLeadingStrain scales prepared.trajectory.movingFamily.patchMotion
      prepared.reference time index +
        relativeStraightenedSaddleStrainRemainder scales (cascadePairedMotion prepared) graph coordinate index time
    let growth := 2 * Real.sqrt 2 * scales.omega (index.val + 1)
    ContinuousOn input (Icc 0 finish) ∧
    (∀ time ∈ Icc 0 finish,
      (relative time).1 = ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (input current).1) ∧
    (∀ time ∈ Icc 0 finish,
      (relative time).2 = ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * (input current).2) ∧
    (∀ time ∈ Icc 0 finish,
      |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * |(input current).2|) ∧
    (∀ weight : ℝ, -growth < weight →
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |(relative time).2|) ≤
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |(input time).2|) / (weight + growth)) := by
  obtain ⟨regularRadius, regularPositive, regularQuarter, regular⟩ :=
    exists_uniform_cascade_paired_chart_regularity graphSmooth coordinateSmooth
  obtain ⟨equationRadius, equationPositive, _, equation⟩ :=
    exists_uniform_cascade_closed_saddle_dynamics graphSmooth coordinateSmooth
  let radius := min regularRadius equationRadius
  refine ⟨radius, lt_min regularPositive equationPositive,
    (min_le_left _ _).trans regularQuarter, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path index nonterminal finish finishNonnegative finishBound small
  let relative := fun time => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
    referenceStraightenedShape prepared.reference graph coordinate index time
  let input := fun time => quadrupoleRelativeLeadingStrain scales prepared.trajectory.movingFamily.patchMotion
    prepared.reference time index +
      relativeStraightenedSaddleStrainRemainder scales (cascadePairedMotion prepared) graph coordinate index time
  let growth := 2 * Real.sqrt 2 * scales.omega (index.val + 1)
  have regularity := regular prepared path index finish finishBound
    (fun side time inside => (small side time inside).trans_le (min_le_left _ _))
  have actual (time : ℝ) (inside : time ∈ Icc 0 finish) :
      HasDerivAt relative ((growth * (relative time).1, -growth * (relative time).2) + input time) time := by
    have derivative := equation prepared path index time ⟨inside.1, inside.2.trans finishBound⟩
      (fun side => (small side time inside).trans_le (min_le_right _ _))
    rw [relativeStraightenedSaddleVelocity_eq_leading_strain] at derivative
    simpa only [relative, input, growth, Prod.fst_sub, Prod.snd_sub, add_assoc] using derivative
  have inputContinuous : ContinuousOn input (Icc 0 finish) := by
    have candidate : ContinuousOn (fun time => deriv relative time -
        (growth * (relative time).1, -growth * (relative time).2)) (Icc 0 finish) :=
      regularity.2.sub ((continuousOn_const.mul regularity.1.fst).prodMk
        (continuousOn_const.mul regularity.1.snd))
    apply candidate.congr
    intro time inside
    change input time = deriv relative time - (growth * (relative time).1, -growth * (relative time).2)
    rw [(actual time inside).deriv]
    abel
  have initial : relative 0 = 0 := prepared.nonterminal_initial_straightened_difference graph coordinate index nonterminal
  have unstableEquation (time : ℝ) (inside : time ∈ Icc 0 finish) :
      HasDerivAt (fun current => (relative current).1)
        (growth * (relative time).1 + (input time).1) time := by
    simpa only [Prod.fst_add] using (actual time inside).fst
  have stableEquation (time : ℝ) (inside : time ∈ Icc 0 finish) :
      HasDerivAt (fun current => (relative current).2)
        (-growth * (relative time).2 + (input time).2) time := by
    simpa only [Prod.snd_add] using (actual time inside).snd
  have unstableIdentity (time : ℝ) (inside : time ∈ Icc 0 finish) :
      (relative time).1 = ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (input current).1 := by
    simpa only [initial, Prod.fst_zero, mul_zero, zero_add] using
      scalar_duhamel_convolution inputContinuous.fst unstableEquation inside.1 inside.2
  have stableIdentity (time : ℝ) (inside : time ∈ Icc 0 finish) :
      (relative time).2 = ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * (input current).2 := by
    simpa only [initial, Prod.snd_zero, mul_zero, zero_add] using
      scalar_duhamel_convolution inputContinuous.snd stableEquation inside.1 inside.2
  have stableBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * |(input current).2| := by
    rw [stableIdentity time inside]
    have bound := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun current => Real.exp (-growth * (time - current)) * (input current).2) inside.1
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using bound
  refine ⟨inputContinuous, unstableIdentity, stableIdentity, stableBound, ?_⟩
  intro weight rateBound
  let extended := fun time : ℝ => |(input (projIcc 0 finish finishNonnegative time)).2|
  have extendedContinuous : Continuous extended :=
    (continuousOn_iff_continuous_restrict.mp inputContinuous.snd.abs).comp continuous_projIcc
  have extendedEqual (time : ℝ) (inside : time ∈ Icc 0 finish) :
      extended time = |(input time).2| := by
    simp only [extended, projIcc_of_mem finishNonnegative inside]
  have responseContinuous : Continuous (EulerNonuniqueness.exponentialResponse (-growth) extended) :=
    continuous_iff_continuousAt.mpr fun time =>
      (EulerNonuniqueness.hasDerivAt_exponentialResponse extendedContinuous (-growth) time).continuousAt
  have pointBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |(relative time).2| ≤ EulerNonuniqueness.exponentialResponse (-growth) extended time := by
    rw [EulerNonuniqueness.exponentialResponse_eq_integral]
    have equal : (∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * extended current) =
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * |(input current).2| := by
      apply intervalIntegral.integral_congr
      intro current member
      rw [uIcc_of_le inside.1] at member
      change Real.exp (-growth * (time - current)) * extended current = _
      rw [extendedEqual current ⟨member.1, member.2.trans inside.2⟩]
    rw [equal]
    exact stableBound time inside
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative
    ((weightContinuous.continuousOn.mul regularity.1.snd.abs).intervalIntegrable_of_Icc finishNonnegative)
    ((weightContinuous.mul responseContinuous).intervalIntegrable 0 finish)
    (fun time inside => mul_le_mul_of_nonneg_left (pointBound time inside) (Real.exp_pos _).le)
  have estimate := EulerNonuniqueness.weighted_exponentialResponse_integral_le extendedContinuous
    rateBound finishNonnegative (fun time inside => by rw [extendedEqual time inside]; exact abs_nonneg _)
  have sourceEqual : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * extended time) =
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |(input time).2| := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le finishNonnegative] at inside
    change Real.exp (-weight * time) * extended time = _
    rw [extendedEqual time inside]
  simpa only [sourceEqual, sub_neg_eq_add] using comparison.trans estimate

end EulerNonuniqueness.Paper
