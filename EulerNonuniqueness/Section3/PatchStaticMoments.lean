import EulerNonuniqueness.Section3.BoundaryRadialTrapping
import EulerNonuniqueness.General.CentroidInertia

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem patchCentroid_eq_setAverage {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    patchCentroid motion time index patch = ⨍ position in motion.domain time index patch, position := by
  rw [patchCentroid, average_eq]
  simp only [Measure.real, Measure.restrict_apply_univ, Complex.real_smul, Complex.ofReal_inv,
    div_eq_mul_inv, mul_comm]

theorem FinitePatchEvolution.patch_centroid_centered_integral_zero {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4) :
    (∫ position in motion.domain time index patch, position - patchCentroid motion time index patch) = 0 := by
  rw [patchCentroid_eq_setAverage]
  exact setAverage_sub_setAverage (evolution.2.2.2.1 time inside index patch).2.1.measure_lt_top.ne
    (fun position : ℂ => position)

theorem FinitePatchEvolution.patch_radial_moment_recenter {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4) (center : ℂ) :
    (∫ position in motion.domain time index patch, ‖position - center‖ ^ 2) =
      (∫ position in motion.domain time index patch, ‖position - patchCentroid motion time index patch‖ ^ 2) +
        (Real.pi * scales.radius (index.val + 1) ^ 2) * ‖patchCentroid motion time index patch - center‖ ^ 2 := by
  have properties := evolution.2.2.2.1 time inside index patch
  have firstIntegrable : IntegrableOn (fun position : ℂ => position) (motion.domain time index patch) :=
    (continuous_id.continuousOn.integrableOn_compact properties.2.1.isCompact_closure).mono_set subset_closure
  have squareIntegrable : IntegrableOn
      (fun position : ℂ => ‖position - patchCentroid motion time index patch‖ ^ 2) (motion.domain time index patch) :=
    (((continuous_id.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      properties.2.1.isCompact_closure).mono_set subset_closure
  have identity := integral_norm_sub_centroid_eq firstIntegrable squareIntegrable properties.2.1.measure_lt_top
    (center := center) (evolution.patch_centroid_centered_integral_zero inside index patch)
  have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
    rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  rw [area] at identity
  linarith

theorem FinitePatchEvolution.integrable_patchDensity_smul_continuous {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) {function : ℂ → value} (continuous : Continuous function) :
    Integrable (fun position => patchDensity scales motion time index patch position • function position) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have functionIntegrable : IntegrableOn function (motion.domain time index patch) :=
    (continuous.continuousOn.integrableOn_compact properties.2.1.isCompact_closure).mono_set subset_closure
  have identity : (fun position => patchDensity scales motion time index patch position • function position) =
      fun position => (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        (motion.domain time index patch).indicator function position := by
    funext position
    by_cases member : position ∈ motion.domain time index patch <;> simp [patchDensity, member]
  rw [identity]
  exact ((integrable_indicator_iff properties.1.measurableSet).mpr functionIntegrable).smul _

theorem FinitePatchEvolution.integral_patchDensity_smul {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) (function : ℂ → value) :
    (∫ position, patchDensity scales motion time index patch position • function position) =
      (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        ∫ position in motion.domain time index patch, function position := by
  have identity : (fun position => patchDensity scales motion time index patch position • function position) =
      fun position => (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        (motion.domain time index patch).indicator function position := by
    funext position
    by_cases member : position ∈ motion.domain time index patch <;> simp [patchDensity, member]
  rw [identity, integral_smul, integral_indicator (evolution.2.2.2.1 time inside index patch).1.measurableSet]

theorem FinitePatchEvolution.integral_quadrupoleDensity_smul_continuous {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) {function : ℂ → value} (continuous : Continuous function) :
    (∫ position, quadrupoleDensity scales motion time index position • function position) =
      ∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        ∫ position in motion.domain time index patch, function position := by
  simp only [quadrupoleDensity, Finset.sum_smul]
  rw [integral_finset_sum _ (fun patch _ => evolution.integrable_patchDensity_smul_continuous inside index patch continuous)]
  exact Finset.sum_congr rfl fun patch _ => evolution.integral_patchDensity_smul inside index patch function

end EulerNonuniqueness.Paper
