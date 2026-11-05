import EulerNonuniqueness.Section6.MovingPatchComplexMoment
import EulerNonuniqueness.Section3.BoundaryRadialTrapping

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_complex_second_moment_point_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) (reference : ℂ)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (control : BoundaryCloseToCircle scales motion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16) :
    ‖(∫ position in motion.domain time index patch, (position - reference) ^ 2) -
        (Real.pi * scales.radius (index.val + 1) ^ 2) •
          (patchCentroid motion time index patch - reference) ^ 2‖ ≤
      128 * Real.pi * scales.radius (index.val + 1) ^ 4 * error := by
  let domain := motion.domain time index patch
  let centroid := patchCentroid motion time index patch
  have properties := evolution.2.2.2.1 time inside index patch
  have finite : volume domain < ⊤ := properties.2.1.measure_lt_top
  have area : volume.real domain = Real.pi * scales.radius (index.val + 1) ^ 2 := by
    rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  have areaPositive : 0 < volume.real domain := by rw [area]; positivity
  have coordinateIntegrable : IntegrableOn (fun position : ℂ => position) domain :=
    (continuous_id.continuousOn.integrableOn_compact properties.2.1.isCompact_closure).mono_set subset_closure
  have centeredIntegrable : IntegrableOn (fun position : ℂ => position - centroid) domain :=
    coordinateIntegrable.sub (integrableOn_const.mpr (Or.inr finite))
  have squareIntegrable : IntegrableOn (fun position : ℂ => (position - centroid) ^ 2) domain :=
    ((((continuous_id.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      properties.2.1.isCompact_closure).mono_set subset_closure)
  have centeredZero : (∫ position in domain, position - centroid) = 0 := by
    rw [integral_sub coordinateIntegrable (integrableOn_const.mpr (Or.inr finite)), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Complex.real_smul]
    change (∫ position in domain, position) - (volume.real domain : ℂ) *
      ((∫ position in domain, position) / (volume.real domain : ℂ)) = 0
    field_simp [Complex.ofReal_ne_zero.mpr areaPositive.ne']
  have trapping := evolution.domain_radial_trapping inside index patch control errorNonnegative
    (by linarith) radiusPositive
  have estimate := Section6.patch_centered_complex_second_moment_of_trapping properties.1.measurableSet
    centroid centroid radiusPositive errorNonnegative errorSmall trapping.1 trapping.2 area centeredZero
  rw [FiniteLiteralPatchFlow.integral_square_recenter domain centroid reference finite centeredIntegrable squareIntegrable centeredZero,
    area, add_sub_cancel_left]
  exact estimate

end EulerNonuniqueness.Paper
