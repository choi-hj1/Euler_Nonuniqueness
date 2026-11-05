import EulerNonuniqueness.Section6.PaperQuadrupoleStrainDerivative

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_strain_multipole
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center location : ℂ)
    (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    HasFDerivAt (biotSavart (quadrupoleDensity scales motion time index))
        (Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) location ∧
      ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location +
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
          8 * (scales.circulation (index.val + 1) : ℂ) * centroidAsymmetry motion time index /
            (location - center) ^ 3 +
          3 * (∫ position, quadrupoleDensity scales motion time index position • (position - center) ^ 2) /
            (location - center) ^ 4)‖ ≤
        352 * scales.circulation (index.val + 1) * radius ^ 3 /
          (Real.pi * ‖location - center‖ ^ 5) := by
  have sourceBound (patch : Fin 4) (position : ℂ) (member : position ∈ motion.domain time index patch) :
      ‖position - center‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBounded patch member
  have sourceSeparated (patch : Fin 4) (position : ℂ) (member : position ∈ motion.domain time index patch) :
      ‖location - center‖ / 2 ≤ ‖location - position‖ := by
    have triangle := norm_add_le (location - position) (position - center)
    rw [sub_add_sub_cancel] at triangle
    linarith [sourceBound patch position member]
  refine ⟨evolution.quadrupole_biotSavart_hasFDerivAt_complexStrain inside index
    (by positivity : 0 < ‖location - center‖ / 2) sourceSeparated, ?_⟩
  have supported : Function.support (quadrupoleDensity scales motion time index) ⊆ Metric.closedBall center radius := by
    intro position member
    by_contra outside
    have zero (patch : Fin 4) : patchDensity scales motion time index patch position = 0 := by
      apply indicator_of_not_mem
      intro insideDomain
      exact outside (sourceBounded patch insideDomain)
    exact member (by simp only [quadrupoleDensity, zero, Finset.sum_const_zero])
  have zeroMean := quadrupoleDensity_integral_zero scales motion time index
    (fun patch => (evolution.2.2.2.1 time inside index patch).1)
    (fun patch => (evolution.2.2.2.1 time inside index patch).2.1)
    (fun patch => (evolution.2.2.2.1 time inside index patch).2.2.1)
    amplitudePositive frequencyPositive ratioPositive
  have estimate := Section6.vorticityComplexStrain_zeroMean_multipole_bound
    (evolution.quadrupoleDensity_integrable inside index) zeroMean radiusNonnegative supported locationPositive separated
  rw [evolution.integral_quadrupoleDensity_first_moment inside amplitudePositive frequencyPositive ratioPositive index center] at estimate
  have firstMomentCoefficient : 2 * ((4 * scales.circulation (index.val + 1)) • centroidAsymmetry motion time index) =
      8 * (scales.circulation (index.val + 1) : ℂ) * centroidAsymmetry motion time index := by
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [firstMomentCoefficient] at estimate
  apply estimate.trans
  have massBound := evolution.quadrupoleDensity_integral_abs_le inside amplitudePositive frequencyPositive ratioPositive index
  have multiplied := mul_le_mul_of_nonneg_left massBound
    (show 0 ≤ 88 * radius ^ 3 / (Real.pi * ‖location - center‖ ^ 5) by positivity)
  convert multiplied using 1 <;> ring

end EulerNonuniqueness.Paper
