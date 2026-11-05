import EulerNonuniqueness.Section6.PaperPatchMomentStrainError
import EulerNonuniqueness.Section6.SourceMomentStrainError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_strain_leadingSource_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center location : ℂ) (outgoingPhase elapsed : ℝ)
    (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location -
        Section6.leadingSourceStrain (scales.circulation (index.val + 1)) ‖location - center‖
          (Complex.arg (location - center)) outgoingPhase elapsed‖ ≤
      4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
          (Real.pi * ‖location - center‖ ^ 3) +
        3 * ‖(∫ position, quadrupoleDensity scales motion time index position • (position - center) ^ 2) -
          Section6.separatingLeadingMoment (scales.circulation (index.val + 1)) outgoingPhase elapsed‖ /
          (2 * Real.pi * ‖location - center‖ ^ 4) +
        352 * scales.circulation (index.val + 1) * radius ^ 3 /
          (Real.pi * ‖location - center‖ ^ 5) := by
  have estimate := evolution.quadrupole_strain_target_moment_error inside amplitudePositive frequencyPositive ratioPositive
    index center location (Section6.separatingLeadingMoment (scales.circulation (index.val + 1)) outgoingPhase elapsed)
    radiusNonnegative sourceBounded locationPositive separated
  have coefficient : -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
      3 * Section6.separatingLeadingMoment (scales.circulation (index.val + 1)) outgoingPhase elapsed /
        (location - center) ^ 4) =
      Section6.leadingSourceStrain (scales.circulation (index.val + 1)) ‖location - center‖
        (Complex.arg (location - center)) outgoingPhase elapsed := by
    rw [Section6.leadingSourceStrain_eq_moment _ _ _ (norm_pos_iff.mp locationPositive)]
    simp only [star_div₀, star_mul, star_pow, Complex.star_def, Complex.conj_ofNat]
    push_cast
    ring
  rw [coefficient] at estimate
  exact estimate

theorem FinitePatchEvolution.quadrupole_rhombus_growing_strain_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center location positive : ℂ)
    (positiveNonzero : positive ≠ 0) (outgoingPhase elapsed : ℝ)
    (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    let negative := Complex.I * (Real.sqrt Section2.rhombusRatio : ℂ) * positive
    let actual := Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location
    let ideal := Section6.leadingSourceStrain (scales.circulation (index.val + 1)) ‖location - center‖
      (Complex.arg (location - center)) outgoingPhase elapsed
    |(Section6.pointShapeForcing positive negative (actual * star positive) (actual * star negative)).1 -
      (Section6.pointShapeForcing positive negative (ideal * star positive) (ideal * star negative)).1| ≤
      4 * (4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
          (Real.pi * ‖location - center‖ ^ 3) +
        3 * ‖(∫ position, quadrupoleDensity scales motion time index position • (position - center) ^ 2) -
          Section6.separatingLeadingMoment (scales.circulation (index.val + 1)) outgoingPhase elapsed‖ /
          (2 * Real.pi * ‖location - center‖ ^ 4) +
        352 * scales.circulation (index.val + 1) * radius ^ 3 /
          (Real.pi * ‖location - center‖ ^ 5)) := by
  dsimp only
  exact (Section6.rhombus_unstable_strain_lipschitz positiveNonzero _ _).trans
    (mul_le_mul_of_nonneg_left (evolution.quadrupole_strain_leadingSource_error inside amplitudePositive frequencyPositive
      ratioPositive index center location outgoingPhase elapsed radiusNonnegative sourceBounded locationPositive separated) (by norm_num))

end EulerNonuniqueness.Paper
