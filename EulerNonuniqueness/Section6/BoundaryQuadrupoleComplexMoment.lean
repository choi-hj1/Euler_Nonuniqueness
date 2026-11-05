import EulerNonuniqueness.Section6.BoundaryPatchComplexMoment
import EulerNonuniqueness.Section6.QuadrupolePatchComplexMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem integral_quadrupoleDensity_smul_of_bounded_domains {count : ℕ}
    (scales : Scales) (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (openDomains : ∀ patch, IsOpen (motion.domain time index patch))
    (boundedDomains : ∀ patch, Bornology.IsBounded (motion.domain time index patch))
    (function : ℂ → ℂ) (continuous : Continuous function) :
    (∫ position, quadrupoleDensity scales motion time index position • function position) =
      ∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        ∫ position in motion.domain time index patch, function position := by
  have identity (patch : Fin 4) :
      (fun position => patchDensity scales motion time index patch position • function position) =
        fun position => (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
          (motion.domain time index patch).indicator function position := by
    funext position
    by_cases member : position ∈ motion.domain time index patch <;> simp [patchDensity, member]
  have integrable (patch : Fin 4) :
      Integrable (fun position => patchDensity scales motion time index patch position • function position) := by
    rw [identity]
    exact ((integrable_indicator_iff (openDomains patch).measurableSet).mpr
      ((continuous.continuousOn.integrableOn_compact (boundedDomains patch).isCompact_closure).mono_set
        subset_closure)).smul _
  simp_rw [quadrupoleDensity, Finset.sum_smul]
  rw [integral_finset_sum _ (fun patch _ => integrable patch)]
  apply Finset.sum_congr rfl
  intro patch _
  rw [identity, integral_smul, integral_indicator (openDomains patch).measurableSet]

theorem FinitePatchEvolution.quadrupole_complex_second_moment_point_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16) :
    let positions : Section6.FourPointConfiguration := fun patch => patchCentroid motion time index patch
    ‖(∫ position, quadrupoleDensity scales motion time index position •
        (position - quadrupoleCenter motion time index) ^ 2) -
      scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment positions‖ ≤
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error := by
  dsimp only
  let center := quadrupoleCenter motion time index
  let density := fun patch => patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have massIdentity (patch : Fin 4) : density patch * (Real.pi * scales.radius (index.val + 1) ^ 2) =
      patchSign patch * scales.circulation (index.val + 1) := by
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    dsimp only [density]
    ring
  have signAbs (patch : Fin 4) : |patchSign patch| = 1 := by
    fin_cases patch <;> norm_num [patchSign]
  have pointIdentity :
      (∑ patch : Fin 4, density patch • ((Real.pi * scales.radius (index.val + 1) ^ 2) •
        (patchCentroid motion time index patch - center) ^ 2)) =
      scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment
        (fun patch => patchCentroid motion time index patch) := by
    simp_rw [smul_smul, massIdentity]
    rw [Section6.fourPointCenteredComplexMoment, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro patch _
    change (patchSign patch * scales.circulation (index.val + 1)) • _ = _
    simp only [Complex.real_smul, Complex.ofReal_mul]
    have sign : patchSign patch = Section6.fourPointSign patch := rfl
    rw [sign]
    change (Section6.fourPointSign patch : ℂ) * (scales.circulation (index.val + 1) : ℂ) *
      (patchCentroid motion time index patch - center) ^ 2 = _
    dsimp only [center, quadrupoleCenter, Section6.fourPointArithmeticCenter]
    ring
  rw [integral_quadrupoleDensity_smul_of_bounded_domains scales motion time index
    (fun patch => (evolution.2.2.2.1 time inside index patch).1)
    (fun patch => (evolution.2.2.2.1 time inside index patch).2.1)
    (fun position => (position - center) ^ 2) ((continuous_id.sub continuous_const).pow 2),
    ← pointIdentity, ← Finset.sum_sub_distrib]
  have individual (patch : Fin 4) :
      ‖density patch • (∫ position in motion.domain time index patch, (position - center) ^ 2) -
        density patch • ((Real.pi * scales.radius (index.val + 1) ^ 2) •
          (patchCentroid motion time index patch - center) ^ 2)‖ ≤
      128 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left
      (evolution.patch_complex_second_moment_point_error inside index patch center radiusPositive
        (control patch) errorNonnegative errorSmall) (abs_nonneg (density patch))).trans_eq
    have massAbs := congrArg abs (massIdentity patch)
    rw [abs_mul (density patch), abs_mul (patchSign patch), signAbs, one_mul, abs_of_nonneg circulationNonnegative,
      abs_of_pos (show 0 < Real.pi * scales.radius (index.val + 1) ^ 2 by positivity)] at massAbs
    calc
      _ = 128 * (|density patch| * (Real.pi * scales.radius (index.val + 1) ^ 2)) *
          scales.radius (index.val + 1) ^ 2 * error := by ring
      _ = _ := by rw [massAbs]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => individual patch)).trans_eq
    (by simp only [Fin.sum_univ_succ]; ring))

theorem FinitePatchEvolution.quadrupole_complex_second_moment_increment_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon firstTime secondTime firstError secondError : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (firstInside : firstTime ∈ Icc 0 horizon) (secondInside : secondTime ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (firstControl : ∀ patch, BoundaryCloseToCircle scales motion firstTime index patch firstError)
    (secondControl : ∀ patch, BoundaryCloseToCircle scales motion secondTime index patch secondError)
    (firstNonnegative : 0 ≤ firstError) (firstSmall : firstError ≤ 1 / 16)
    (secondNonnegative : 0 ≤ secondError) (secondSmall : secondError ≤ 1 / 16) :
    let moment := fun time => ∫ position, quadrupoleDensity scales motion time index position •
      (position - quadrupoleCenter motion time index) ^ 2
    let pointMoment := fun time => Section6.fourPointCenteredComplexMoment
      (fun patch => patchCentroid motion time index patch)
    ‖moment secondTime - moment firstTime -
        scales.circulation (index.val + 1) • (pointMoment secondTime - pointMoment firstTime)‖ ≤
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 *
        (secondError + firstError) := by
  dsimp only
  have first := evolution.quadrupole_complex_second_moment_point_error firstInside amplitudePositive
    frequencyPositive ratioPositive index firstControl firstNonnegative firstSmall
  have second := evolution.quadrupole_complex_second_moment_point_error secondInside amplitudePositive
    frequencyPositive ratioPositive index secondControl secondNonnegative secondSmall
  rw [smul_sub]
  have identity :
      (∫ position, quadrupoleDensity scales motion secondTime index position •
          (position - quadrupoleCenter motion secondTime index) ^ 2) -
        (∫ position, quadrupoleDensity scales motion firstTime index position •
          (position - quadrupoleCenter motion firstTime index) ^ 2) -
        (scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment
          (fun patch => patchCentroid motion secondTime index patch) -
          scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment
          (fun patch => patchCentroid motion firstTime index patch)) =
      ((∫ position, quadrupoleDensity scales motion secondTime index position •
          (position - quadrupoleCenter motion secondTime index) ^ 2) -
        scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment
          (fun patch => patchCentroid motion secondTime index patch)) -
      ((∫ position, quadrupoleDensity scales motion firstTime index position •
          (position - quadrupoleCenter motion firstTime index) ^ 2) -
        scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment
          (fun patch => patchCentroid motion firstTime index patch)) := by abel
  rw [identity]
  exact (norm_sub_le _ _).trans ((add_le_add second first).trans_eq (by ring))

end EulerNonuniqueness.Paper
