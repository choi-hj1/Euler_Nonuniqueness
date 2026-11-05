import EulerNonuniqueness.Section3.PatchStaticMoments
import EulerNonuniqueness.Section6.PatchRadialInertia
import EulerNonuniqueness.Section6.QuadrupolePatchAngularInertia

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_radial_inertia_bound_of_boundaryControl
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4)
    (control : BoundaryCloseToCircle scales motion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusPositive : 0 < scales.radius (index.val + 1)) :
    |(∫ position in motion.domain time index patch, ‖position - patchCentroid motion time index patch‖ ^ 2) -
        Real.pi * scales.radius (index.val + 1) ^ 4 / 2| ≤
      12 * Real.pi * scales.radius (index.val + 1) ^ 4 * error ^ 2 := by
  have properties := evolution.2.2.2.1 time inside index patch
  have trapping := evolution.domain_radial_trapping inside index patch control errorNonnegative
    (show error < 1 / 4 by linarith) radiusPositive
  have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
    rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  exact Section6.patch_radial_inertia_difference_bound properties.1.measurableSet
    (patchCentroid motion time index patch) radiusPositive errorNonnegative (by linarith)
    trapping.1 trapping.2 area

theorem FinitePatchEvolution.quadrupole_angular_inertia_bound_of_boundaryControl
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (control : ∀ patch : Fin 4, BoundaryCloseToCircle scales motion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16) :
    |angularImpulse scales motion time index -
        2 * scales.circulation (index.val + 1) * diagonalDifference motion time index| ≤
      48 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error ^ 2 := by
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have massIdentity (patch : Fin 4) :
      (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
        (Real.pi * scales.radius (index.val + 1) ^ 2) = patchSign patch * scales.circulation (index.val + 1) := by
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    ring
  have signAbs (patch : Fin 4) : |patchSign patch| = 1 := by
    fin_cases patch <;> norm_num [patchSign]
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have integralIdentity : angularImpulse scales motion time index =
      ∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
        (∫ position in motion.domain time index patch, ‖position - quadrupoleCenter motion time index‖ ^ 2) := by
    calc
      _ = ∫ position, quadrupoleDensity scales motion time index position •
          ‖position - quadrupoleCenter motion time index‖ ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun position => mul_comm _ _
      _ = _ := by
        simpa only [smul_eq_mul] using evolution.integral_quadrupoleDensity_smul_continuous inside index
          (((continuous_id.sub continuous_const).norm).pow 2)
  have pointIdentity :
      (∑ patch : Fin 4, ((patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
          (Real.pi * scales.radius (index.val + 1) ^ 2)) *
          ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ^ 2) =
        2 * scales.circulation (index.val + 1) * diagonalDifference motion time index := by
    simp_rw [massIdentity]
    calc
      _ = scales.circulation (index.val + 1) *
          ∑ patch : Fin 4, patchSign patch *
            ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro patch _
        ring
      _ = _ := by rw [quadrupole_centroid_angular_identity]; ring
  have diskCancellation :
      (∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
        (Real.pi * scales.radius (index.val + 1) ^ 4 / 2)) = 0 := by
    norm_num [Fin.sum_univ_succ, patchSign]
  have errorIdentity : angularImpulse scales motion time index -
      2 * scales.circulation (index.val + 1) * diagonalDifference motion time index =
      ∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
        ((∫ position in motion.domain time index patch, ‖position - patchCentroid motion time index patch‖ ^ 2) -
          Real.pi * scales.radius (index.val + 1) ^ 4 / 2) := by
    rw [integralIdentity, ← pointIdentity]
    calc
      _ = ((∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
          (∫ position in motion.domain time index patch, ‖position - quadrupoleCenter motion time index‖ ^ 2)) -
          ∑ patch : Fin 4, ((patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
            (Real.pi * scales.radius (index.val + 1) ^ 2)) *
            ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ^ 2) -
          ∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
            (Real.pi * scales.radius (index.val + 1) ^ 4 / 2) := by rw [diskCancellation, sub_zero]
      _ = _ := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro patch _
        rw [evolution.patch_radial_moment_recenter inside index patch (quadrupoleCenter motion time index)]
        ring
  rw [errorIdentity]
  change ‖∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
    ((∫ position in motion.domain time index patch, ‖position - patchCentroid motion time index patch‖ ^ 2) -
      Real.pi * scales.radius (index.val + 1) ^ 4 / 2)‖ ≤ _
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _patch : Fin 4,
        12 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error ^ 2 := by
      apply Finset.sum_le_sum
      intro patch _
      rw [Real.norm_eq_abs, abs_mul]
      have estimate := mul_le_mul_of_nonneg_left
        (evolution.patch_radial_inertia_bound_of_boundaryControl inside index patch (control patch)
          errorNonnegative errorSmall radiusPositive)
        (abs_nonneg (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4))
      apply estimate.trans_eq
      have signedMass : |patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4| *
          (Real.pi * scales.radius (index.val + 1) ^ 2) = scales.circulation (index.val + 1) := by
        calc
          _ = |(patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
              (Real.pi * scales.radius (index.val + 1) ^ 2)| := by
            symm
            rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * scales.radius (index.val + 1) ^ 2 by positivity)]
          _ = |patchSign patch * scales.circulation (index.val + 1)| := by rw [massIdentity]
          _ = _ := by rw [abs_mul, signAbs, one_mul, abs_of_nonneg circulationNonnegative]
      calc
        _ = 12 * (|patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4| *
            (Real.pi * scales.radius (index.val + 1) ^ 2)) * scales.radius (index.val + 1) ^ 2 * error ^ 2 := by ring
        _ = _ := by rw [signedMass]
    _ = _ := by simp only [Fin.sum_univ_succ]; ring

end EulerNonuniqueness.Paper
