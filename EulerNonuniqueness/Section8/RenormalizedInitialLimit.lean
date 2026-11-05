import EulerNonuniqueness.Section8.InitialAETrace
import EulerNonuniqueness.Section8.RenormalizationL2
import EulerNonuniqueness.Section8.TestSlices

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem integrable_renormalization_mul_of_memLp_two
    {source coefficient : Vorticity} (sourceMember : MemLp source 2 volume)
    (coefficientMember : MemLp coefficient 2 volume) (coefficientIntegrable : Integrable coefficient)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization) :
    Integrable (fun position => renormalization (source position) * coefficient position) := by
  obtain ⟨bound, nonnegative, bounded⟩ := admissible.exists_norm_sub_bound
  have shiftedMember := (memLp_renormalization_sub_two sourceMember (MemLp.zero : MemLp (0 : Vorticity) 2 volume)
    admissible.1.continuous nonnegative bounded).1
  have shiftedIntegrable := memLp_one_iff_integrable.mp (shiftedMember.mul coefficientMember)
  have integrable := shiftedIntegrable.add (coefficientIntegrable.const_mul (renormalization 0))
  convert integrable using 1
  funext position
  simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply]
  ring

theorem TransportAnalyticHypotheses.renormalized_mollified_initial_pairing_limit
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    {test : ℝ × Plane → ℝ} (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test) :
    Integrable (fun position => renormalization (initial position) * test (0, position)) ∧
      Tendsto (fun index => ∫ position, renormalization (mollification initial index position) * test (0, position))
        atTop (𝓝 (∫ position, renormalization (initial position) * test (0, position))) := by
  let coefficient := fun position => test (0, position)
  have coefficientContinuous := (contDiff_spatial_slice testSmooth 0).continuous
  have coefficientCompact := hasCompactSupport_spatial_slice testCompact 0
  have coefficientMember : MemLp coefficient 2 volume := coefficientContinuous.memLp_of_hasCompactSupport coefficientCompact
  have coefficientIntegrable : Integrable coefficient := coefficientContinuous.integrable_of_hasCompactSupport coefficientCompact
  have zeroInside : (0 : ℝ) ∈ Icc 0 horizon := ⟨le_rfl, positive.le⟩
  have sourceMember := hypotheses.weakL2Continuous.1 0 zeroInside
  have targetIntegrable := integrable_renormalization_mul_of_memLp_two sourceMember coefficientMember coefficientIntegrable admissible
  have initialEquality : (fun position => renormalization (omega 0 position) * coefficient position) =ᵐ[volume]
      (fun position => renormalization (initial position) * coefficient position) := by
    filter_upwards [hypotheses.initial_ae_eq positive] with position equality
    rw [equality]
  refine ⟨targetIntegrable.congr initialEquality, ?_⟩
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  obtain ⟨bound, nonnegative, bounded⟩ := admissible.exists_norm_sub_bound
  have mollifiedMembers (index : ℕ) : MemLp (mollification (omega 0) index) 2 volume :=
    (contDiff_mollification (hypotheses.integrable zeroInside) index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification (supported 0 zeroInside) index)
  have sequenceIntegrable (index : ℕ) := integrable_renormalization_mul_of_memLp_two
    (mollifiedMembers index) coefficientMember coefficientIntegrable admissible
  have sourceConverges := tendsto_eLpNorm_mollification_sub
    (fun exponent exponentBound => hypotheses.membership exponent exponentBound 0 zeroInside)
    (supported 0 zeroInside) (exponent := 2) (by norm_num)
  have sourceRealConverges := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp sourceConverges
  simp only [Function.comp_apply, ENNReal.ofReal_ofNat, ENNReal.toReal_zero] at sourceRealConverges
  have errorConverges : Tendsto (fun index => ∫ position,
      (renormalization (mollification (omega 0) index position) - renormalization (omega 0 position)) * coefficient position)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have boundConverges := (tendsto_const_nhds (x := bound * (eLpNorm coefficient 2 volume).toReal)).mul sourceRealConverges
    apply squeeze_zero (fun _ => norm_nonneg _) (fun index => ?_)
      (by simpa only [ENNReal.toReal_zero, ENNReal.ofReal_ofNat, mul_zero] using boundConverges)
    have result := memLp_renormalization_sub_two (mollifiedMembers index) sourceMember admissible.1.continuous nonnegative bounded
    calc
      _ ≤ ∫ position, ‖(renormalization (mollification (omega 0) index position) - renormalization (omega 0 position)) * coefficient position‖ :=
        norm_integral_le_integral_norm _
      _ ≤ (eLpNorm (fun position => renormalization (mollification (omega 0) index position) - renormalization (omega 0 position)) 2 volume).toReal *
          (eLpNorm coefficient 2 volume).toReal := by
        simpa only [norm_mul] using integral_norm_mul_norm_le_eLpNorm_two result.1 coefficientMember
      _ ≤ (bound * (eLpNorm (mollification (omega 0) index - omega 0) 2 volume).toReal) *
          (eLpNorm coefficient 2 volume).toReal := mul_le_mul_of_nonneg_right result.2 ENNReal.toReal_nonneg
      _ = _ := by ac_rfl
  have errorIdentity (index : ℕ) : (∫ position,
      (renormalization (mollification (omega 0) index position) - renormalization (omega 0 position)) * coefficient position) =
      (∫ position, renormalization (mollification (omega 0) index position) * coefficient position) -
        ∫ position, renormalization (omega 0 position) * coefficient position := by
    simp only [sub_mul]
    exact integral_sub (sequenceIntegrable index) targetIntegrable
  simp_rw [errorIdentity] at errorConverges
  have result := errorConverges.add (tendsto_const_nhds (x := ∫ position, renormalization (omega 0 position) * coefficient position))
  simp only [sub_add_cancel, zero_add] at result
  rw [integral_congr_ae initialEquality] at result
  apply result.congr'
  filter_upwards [] with index
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun position => by
    dsimp only [coefficient]
    rw [hypotheses.mollification_initial_trace positive]

end EulerNonuniqueness
