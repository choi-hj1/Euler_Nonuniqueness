import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget
import EulerNonuniqueness.General.ComplexPhaseUniqueness

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_reference_phase_drift_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {referenceConstant tolerance : ℝ} (referenceNonnegative : 0 ≤ referenceConstant)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {threshold scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency}
        orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius
        factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      ∃ referenceLift : ℝ → Fin count → ℝ,
        ReferencePhaseLift prepared.reference (fun index => phase (index.val + 1)) referenceLift ∧
        ∀ (index : Fin count) (finish : ℝ), 0 ≤ finish → finish ≤ path.stop →
        ∀ lift : ℝ → ℝ, ContinuousOn lift (Icc 0 finish) →
          lift 0 = phase (index.val + 1) →
          (∀ time ∈ Icc 0 finish,
            positiveHalfDiagonal prepared.reference time index =
              (‖positiveHalfDiagonal prepared.reference time index‖ : ℂ) *
                Complex.exp (Complex.I * (lift time : ℂ))) →
          EqOn lift (fun time => referenceLift time index) (Icc 0 finish) ∧
          ∀ time ∈ Icc 0 finish,
            |lift time - phase (index.val + 1) +
              ({scales with frequency := frequency} : Scales).omega (index.val + 1) * time| <
                tolerance := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
      referenceNonnegative tolerancePositive] with frequency frequencyOne budgets
  intro orbit sectionTime phase dipoleAngle threshold scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by
    change 0 < scales.ratio
    linarith only [ratioBound]
  obtain ⟨unstable, referenceLift, initial, referencePolar, evolution, coarse, sharp⟩ :=
    prepared.referenceSolution
  refine ⟨referenceLift, referencePolar, ?_⟩
  intro index finish finishNonnegative finishBound lift liftContinuous liftInitial liftPolar
  have finishOne : finish ≤ 1 := finishBound.trans path.stopBound
  have referenceInside (time : ℝ) (inside : time ∈ Icc 0 finish) :
      time ∈ Icc (0 : ℝ) 2 :=
    ⟨inside.1, by linarith only [inside.2, finishOne]⟩
  have referenceNonzero (time : ℝ) (inside : time ∈ Icc 0 finish) :
      positiveHalfDiagonal prepared.reference time index ≠ 0 := by
    have lower := (coarse.2.1 time (referenceInside time inside) index).2.2.1
    have scaled := (le_div_iff₀
      (sq_pos_of_pos (changed.length_pos (index.val + 1)))).mp lower
    have differencePositive : 0 < diagonalDifference prepared.reference time index := by
      nlinarith only [scaled, sq_pos_of_pos (changed.length_pos (index.val + 1))]
    intro zero
    change 0 < ‖positiveHalfDiagonal prepared.reference time index‖ ^ 2 -
      ‖negativeHalfDiagonal prepared.reference time index‖ ^ 2 at differencePositive
    rw [zero, norm_zero] at differencePositive
    nlinarith only [differencePositive,
      sq_nonneg ‖negativeHalfDiagonal prepared.reference time index‖]
  have referenceEquality : EqOn lift (fun time => referenceLift time index) (Icc 0 finish) := by
    apply General.phase_polar_lift_unique_on_Icc finishNonnegative liftContinuous
      ((referencePolar index).1.mono (fun time inside => referenceInside time inside))
      (liftInitial.trans (referencePolar index).2.1.symm) referenceNonzero liftPolar
    intro time inside
    exact (referencePolar index).2.2 time (referenceInside time inside)
  refine ⟨referenceEquality, ?_⟩
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have envelopeSmall : referenceConstant * (changed.strain + changed.strain ^ 2 +
      (changed.omega (index.val + 1))⁻¹ ^ 4) < tolerance := by
    have current := (budgets (index.val + 1)).2
    have identity : changed.omega (index.val + 1) * (referenceConstant *
        ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
          (changed.omega (index.val + 1))⁻¹ ^ 5)) =
        referenceConstant * (changed.strain + changed.strain ^ 2 +
          (changed.omega (index.val + 1))⁻¹ ^ 4) := by
      field_simp [omegaPositive.ne']
      ring
    change changed.omega (index.val + 1) * _ < tolerance at current
    rw [identity] at current
    exact current
  intro time inside
  rw [referenceEquality inside]
  have actual := (sharp.1 1 (by norm_num) le_rfl time
    ⟨inside.1, inside.2.trans finishOne⟩ index).2
  have actualBound : |referenceLift time index - phase (index.val + 1) +
      changed.omega (index.val + 1) * time| ≤ referenceConstant *
        (changed.strain + changed.strain ^ 2 +
          (changed.omega (index.val + 1))⁻¹ ^ 4) := by
    simpa only [one_mul, mul_one] using actual
  exact actualBound.trans_lt envelopeSmall

end EulerNonuniqueness.Paper
