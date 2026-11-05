import EulerNonuniqueness.Section8.TimeFluxContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.uniform_transportFlux_bound
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
      ‖∫ position, sequence index time position *
        fderiv ℝ test position (biotSavart (sequence index time) position)‖ ≤ bound := by
  obtain ⟨rawOperatorBound, rawOperatorBounded⟩ :=
    (compact.fderiv ℝ).exists_bound_of_continuous (smooth.continuous_fderiv (by simp))
  let operatorBound := max rawOperatorBound 0
  have operatorNonnegative : 0 ≤ operatorBound := le_max_right _ _
  have operatorBounded (position : Plane) : ‖fderiv ℝ test position‖ ≤ operatorBound :=
    (rawOperatorBounded position).trans (le_max_left _ _)
  obtain ⟨vorticityBound, vorticityBoundFinite, vorticityBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨dominator, dominatorMember, velocityBounded⟩ :=
    hypotheses.biotSavart_L2_dominator horizonNonnegative
  refine ⟨vorticityBound.toReal * (operatorBound * (eLpNorm dominator 2 volume).toReal),
    by positivity, ?_⟩
  intro index time timeBound
  have vorticityMember := (hypotheses.2.2 index).2.1.1 time timeBound
  have velocityMember := hypotheses.biotSavart_memLp_two index timeBound
  have scalarMember : MemLp (fun position =>
      fderiv ℝ test position (biotSavart (sequence index time) position)) 2 volume :=
    velocityMember.apply_bounded_continuousLinearMap
      (smooth.continuous_fderiv (by simp)).aestronglyMeasurable operatorBounded
  have scalarNormBound : eLpNorm (fun position =>
      fderiv ℝ test position (biotSavart (sequence index time) position)) 2 volume ≤
      ENNReal.ofReal operatorBound * eLpNorm dominator 2 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    exact Eventually.of_forall fun position =>
      ((fderiv ℝ test position).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (operatorBounded position) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (velocityBounded index time timeBound position)
            operatorNonnegative))
  have scalarRealBound : (eLpNorm (fun position =>
      fderiv ℝ test position (biotSavart (sequence index time) position)) 2 volume).toReal ≤
      operatorBound * (eLpNorm dominator 2 volume).toReal := by
    have finite : ENNReal.ofReal operatorBound * eLpNorm dominator 2 volume ≠ ∞ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top dominatorMember.eLpNorm_lt_top).ne
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal operatorNonnegative] using
      ENNReal.toReal_mono finite scalarNormBound
  have vorticityRealBound : (eLpNorm (sequence index time) 2 volume).toReal ≤
      vorticityBound.toReal := ENNReal.toReal_mono vorticityBoundFinite.ne
        (by simpa using vorticityBounded index time timeBound)
  have holder := norm_integral_smul_le_eLpNorm Real.HolderConjugate.two_two
    (show MemLp (sequence index time) (ENNReal.ofReal (2 : ℝ)) volume by
      simpa using vorticityMember)
    (show MemLp (fun position =>
      fderiv ℝ test position (biotSavart (sequence index time) position))
      (ENNReal.ofReal (2 : ℝ)) volume by simpa using scalarMember)
  apply (show ‖∫ position, sequence index time position *
      fderiv ℝ test position (biotSavart (sequence index time) position)‖ ≤
      (eLpNorm (sequence index time) 2 volume).toReal *
        (eLpNorm (fun position => fderiv ℝ test position
          (biotSavart (sequence index time) position)) 2 volume).toReal by
    simpa only [smul_eq_mul, ENNReal.ofReal_ofNat] using holder).trans
  exact mul_le_mul vorticityRealBound scalarRealBound ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg

end EulerNonuniqueness
