import EulerNonuniqueness.Section6.PatchSubfamilyRadialInertia
import EulerNonuniqueness.Section6.QuadrupoleMaterialMoments
import EulerNonuniqueness.Section6.FourPointAngularImpulse

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem quadrupole_centroid_angular_identity {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    (∑ patch : Fin 4, patchSign patch *
      ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ^ 2) =
        2 * diagonalDifference motion time index := by
  exact Section6.fourPointAngularImpulse_at_arithmeticCenter
    (fun patch => patchCentroid motion time index patch)

namespace FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

theorem quadrupole_angular_impulse_point_error {count : ℕ}
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
    (referenceCenter : Fin (count * 4) → ℂ) (error : Fin (count * 4) → ℝ)
    (errorNonnegative : ∀ patch : Fin 4, 0 ≤ error (finProdFinEquiv (index, patch)))
    (errorSmall : ∀ patch : Fin 4, error (finProdFinEquiv (index, patch)) ≤ 1 / 16)
    (lower : ∀ patch : Fin 4,
      Metric.ball (referenceCenter (finProdFinEquiv (index, patch)))
        (configuration.radius (finProdFinEquiv (index, patch)) * (1 - error (finProdFinEquiv (index, patch)))) ⊆
          flow.domain time (finProdFinEquiv (index, patch)))
    (upper : ∀ patch : Fin 4,
      flow.domain time (finProdFinEquiv (index, patch)) ⊆
        Metric.ball (referenceCenter (finProdFinEquiv (index, patch)))
          (configuration.radius (finProdFinEquiv (index, patch)) * (1 + error (finProdFinEquiv (index, patch))))) :
    |angularImpulse scales flow.patchMotion time index -
        2 * scales.circulation (index.val + 1) * diagonalDifference flow.patchMotion time index| ≤
      76 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 *
        ∑ patch : Fin 4, error (finProdFinEquiv (index, patch)) ^ 2 := by
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
  have liftCondition {predicate : Fin (count * 4) → Prop}
      (condition : ∀ patch : Fin 4, predicate (finProdFinEquiv (index, patch))) :
      ∀ label ∈ quadrupolePatchLabels index, predicate label := by
    intro label member
    obtain ⟨patch, _, equality⟩ := Finset.mem_image.mp member
    subst label
    exact condition patch
  have estimate := flow.subfamily_radial_second_moment_point_error inside
    (quadrupolePatchLabels index) (quadrupoleCenter flow.patchMotion time index) referenceCenter error
    (liftCondition errorNonnegative) (liftCondition errorSmall) (liftCondition lower) (liftCondition upper)
  have integralIdentity :
      (∫ position, flow.subfamilyVorticity (quadrupolePatchLabels index) time position *
        ‖position - quadrupoleCenter flow.patchMotion time index‖ ^ 2) =
        angularImpulse scales flow.patchMotion time index := by
    rw [← flow.quadrupoleDensity_eq_subfamily scales densityEquation]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun position => mul_comm _ _
  have pointIdentity :
      (∑ label ∈ quadrupolePatchLabels index,
        (configuration.density label * (Real.pi * configuration.radius label ^ 2)) *
          ‖flow.centroid time label - quadrupoleCenter flow.patchMotion time index‖ ^ 2) =
        2 * scales.circulation (index.val + 1) * diagonalDifference flow.patchMotion time index := by
    unfold quadrupolePatchLabels
    rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
    simp_rw [massIdentity, ← flow.patchCentroid_eq_centroid inside]
    calc
      _ = scales.circulation (index.val + 1) *
          ∑ patch : Fin 4, patchSign patch *
            ‖patchCentroid flow.patchMotion time index patch - quadrupoleCenter flow.patchMotion time index‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro patch _
        ring
      _ = _ := by rw [quadrupole_centroid_angular_identity]; ring
  have diskCancellation : (∑ label ∈ quadrupolePatchLabels index,
      configuration.density label * (Real.pi * configuration.radius label ^ 4 / 2)) = 0 := by
    unfold quadrupolePatchLabels
    rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
    simp_rw [densityEquation, radiusEquation]
    simp only [Fin.sum_univ_succ, patchSign, Fin.reduceFinMk]
    norm_num
  rw [integralIdentity, pointIdentity, diskCancellation, sub_zero] at estimate
  apply estimate.trans_eq
  unfold quadrupolePatchLabels
  rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
  simp_rw [massIdentity, radiusEquation, abs_mul, signAbs, one_mul,
    abs_of_nonneg circulationNonnegative]
  rw [← Finset.mul_sum]

end FiniteLiteralPatchFlow

end EulerNonuniqueness.Paper
