import EulerNonuniqueness.Section6.PatchSubfamilyComplexMoment
import EulerNonuniqueness.Section6.QuadrupoleMaterialMoments
import EulerNonuniqueness.Section6.DipoleQuadraticMoment
import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem fourPointCenteredComplexMoment_negativeLabelSwap (positions : FourPointConfiguration) :
    fourPointCenteredComplexMoment (relabelNegativePoints positions) = fourPointCenteredComplexMoment positions := by
  simp [fourPointCenteredComplexMoment, fourPointArithmeticCenter, relabelNegativePoints,
    negativeLabelSwap, Equiv.swap_apply_def, fourPointSign, Fin.sum_univ_succ]
  ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

theorem quadrupole_complex_second_moment_point_error {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (small : ∀ patch : Fin 4,
      ‖flow.shape time (finProdFinEquiv (index, patch)) - standardCircleBanach‖ ≤ 1 / 16) :
    let positions : Section6.FourPointConfiguration := fun patch => flow.centroid time (finProdFinEquiv (index, patch))
    ‖(∫ position, quadrupoleDensity scales flow.patchMotion time index position •
        (position - Section6.fourPointArithmeticCenter positions) ^ 2) -
      scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment positions‖ ≤
      128 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 *
        ∑ patch : Fin 4, ‖flow.shape time (finProdFinEquiv (index, patch)) - standardCircleBanach‖ := by
  let positions : Section6.FourPointConfiguration := fun patch => flow.centroid time (finProdFinEquiv (index, patch))
  let center := Section6.fourPointArithmeticCenter positions
  have massIdentity (patch : Fin 4) :
      configuration.density (finProdFinEquiv (index, patch)) *
          (Real.pi * configuration.radius (finProdFinEquiv (index, patch)) ^ 2) =
        patchSign patch * scales.circulation (index.val + 1) := by
    rw [densityEquation, radiusEquation,
      ← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    ring
  have circulationNonnegative : 0 ≤ scales.circulation (index.val + 1) :=
    (scales.circulation_pos frequencyPositive ratioPositive _).le
  have signAbs (patch : Fin 4) : |patchSign patch| = 1 := by
    fin_cases patch <;> norm_num [patchSign]
  have estimate := flow.subfamily_complex_second_moment_integral_point_error inside
    (quadrupolePatchLabels index) center (fun label member => by
      obtain ⟨patch, _, equality⟩ := Finset.mem_image.mp member
      subst label
      exact small patch)
  rw [← flow.quadrupoleDensity_eq_subfamily scales densityEquation time index] at estimate
  have pointIdentity :
      (∑ label ∈ quadrupolePatchLabels index,
        (configuration.density label * (Real.pi * configuration.radius label ^ 2)) •
          (flow.centroid time label - center) ^ 2) =
        scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment positions := by
    unfold quadrupolePatchLabels
    rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
    simp_rw [massIdentity]
    rw [Section6.fourPointCenteredComplexMoment, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro patch _
    change (patchSign patch * scales.circulation (index.val + 1)) • (positions patch - center) ^ 2 = _
    simp only [Complex.real_smul, Complex.ofReal_mul]
    change (patchSign patch : ℂ) * (scales.circulation (index.val + 1) : ℂ) *
      (positions patch - center) ^ 2 = _
    have sign : patchSign patch = Section6.fourPointSign patch := rfl
    rw [sign]
    ring
  rw [pointIdentity] at estimate
  apply estimate.trans_eq
  unfold quadrupolePatchLabels
  rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
  simp_rw [massIdentity, radiusEquation, abs_mul, signAbs, one_mul,
    abs_of_nonneg circulationNonnegative]
  rw [← Finset.mul_sum]

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
