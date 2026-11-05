import EulerNonuniqueness.Section6.PaperAngularMomentDynamics
import EulerNonuniqueness.Section6.PaperCentroidEndpoints

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_moments_continuousOn_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) :
    ContinuousOn (fun time => angularImpulse scales motion time index) (Icc 0 horizon) ∧
      ContinuousOn (fun time => diagonalDifference motion time index) (Icc 0 horizon) ∧
      ContinuousOn (fun time => quadrupoleCenter motion time index) (Icc 0 horizon) ∧
      ContinuousOn (fun time => centroidAsymmetry motion time index) (Icc 0 horizon) := by
  have centroids (patch : Fin 4) := (evolution.patchCentroid_closed_derivative_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch).1
  have centerContinuous : ContinuousOn (fun time => quadrupoleCenter motion time index) (Icc 0 horizon) :=
    (continuousOn_finset_sum Finset.univ fun patch _ => centroids patch).div_const 4
  have asymmetryContinuous : ContinuousOn (fun time => centroidAsymmetry motion time index) (Icc 0 horizon) :=
    ((((centroids 0).add (centroids 1)).sub (centroids 2)).sub (centroids 3)).div_const 4
  have differenceContinuous : ContinuousOn (fun time => diagonalDifference motion time index) (Icc 0 horizon) :=
    (((centroids 0).sub (centroids 1)).div_const 2).norm.pow 2 |>.sub
      ((((centroids 2).sub (centroids 3)).div_const 2).norm.pow 2)
  have weightIntegrable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
      (time : ℝ) (inside : time ∈ Icc 0 horizon) (function : ℂ → Value) (continuous : Continuous function) :
      Integrable (fun position => quadrupoleDensity scales motion time index position • function position) := by
    simp only [quadrupoleDensity, Finset.sum_smul]
    exact integrable_finset_sum _ (fun patch _ => evolution.integrable_patchDensity_smul_continuous inside index patch continuous)
  have secondIdentity (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      (∫ position, quadrupoleDensity scales motion time index position * ‖position‖ ^ 2) =
        ∑ patch : Fin 4, ∫ position, patchDensity scales motion time index patch position * ‖position‖ ^ 2 := by
    simp only [quadrupoleDensity, Finset.sum_mul]
    exact integral_finset_sum _ (fun patch _ => by
      simpa only [smul_eq_mul] using evolution.integrable_patchDensity_smul_continuous inside index patch (continuous_norm.pow 2))
  have secondContinuous : ContinuousOn (fun time => ∫ position,
      quadrupoleDensity scales motion time index position * ‖position‖ ^ 2) (Icc 0 horizon) := by
    apply (continuousOn_finset_sum Finset.univ fun patch _ =>
      (evolution.patch_supported_smooth_moment_closed_derivative_of_boundary_gaps horizonPositive amplitudePositive
        frequencyPositive ratioPositive radiusPositive control separated index patch (contDiff_norm_sq ℝ)).1).congr
    exact secondIdentity
  have identity (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      angularImpulse scales motion time index =
        (∫ position, quadrupoleDensity scales motion time index position * ‖position‖ ^ 2) -
          2 * @inner ℝ ℂ _ (quadrupoleCenter motion time index)
            ((4 * scales.circulation (index.val + 1)) • centroidAsymmetry motion time index) := by
    have properties := evolution.2.2.2.1 time inside index
    have zeroMass := quadrupoleDensity_integral_zero scales motion time index
      (fun patch => (properties patch).1) (fun patch => (properties patch).2.1)
      (fun patch => (properties patch).2.2.1) amplitudePositive frequencyPositive ratioPositive
    have firstIdentity := evolution.integral_quadrupoleDensity_first_moment inside amplitudePositive
      frequencyPositive ratioPositive index 0
    simp only [sub_zero] at firstIdentity
    have secondIntegrable : Integrable (fun position => quadrupoleDensity scales motion time index position * ‖position‖ ^ 2) := by
      simpa only [smul_eq_mul] using weightIntegrable time inside (fun position : ℂ => ‖position‖ ^ 2) (continuous_norm.pow 2)
    have expansion := integral_weighted_norm_sub_sq (evolution.quadrupoleDensity_integrable inside index)
      (weightIntegrable time inside (fun position : ℂ => position) continuous_id) secondIntegrable
      (quadrupoleCenter motion time index)
    rw [zeroMass, mul_zero, add_zero, firstIdentity] at expansion
    refine (show angularImpulse scales motion time index = ∫ position,
      quadrupoleDensity scales motion time index position * ‖position - quadrupoleCenter motion time index‖ ^ 2 from ?_).trans expansion
    unfold angularImpulse
    exact integral_congr_ae (Filter.Eventually.of_forall fun position => mul_comm _ _)
  refine ⟨?_, differenceContinuous, centerContinuous, asymmetryContinuous⟩
  apply (secondContinuous.sub (continuousOn_const.mul
    (centerContinuous.inner (asymmetryContinuous.const_smul (4 * scales.circulation (index.val + 1)))))).congr
  exact identity

end EulerNonuniqueness.Paper
