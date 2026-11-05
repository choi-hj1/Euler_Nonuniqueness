import EulerNonuniqueness.Section4.ReferenceMaterialCoarsePreparation
import EulerNonuniqueness.Section4.UniversalPaperReferenceSharpBounds
import EulerNonuniqueness.Section4.UniversalReferenceOuterDisplacement
import EulerNonuniqueness.Section4.OuterDisplacementDecay

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000

theorem exists_uniform_reference_material_solutions
    {alpha ratio : ℝ} (alphaPositive : 0 < alpha) (ratioLarge : 2 ≤ ratio) :
    ∃ thresholdMax > (0 : ℝ), ∀ threshold : ℝ, 0 < threshold → threshold ≤ thresholdMax →
    ∃ amplitudeMin > (0 : ℝ), ∀ amplitude : ℝ, amplitudeMin ≤ amplitude →
    ∃ constant > (0 : ℝ), constant ≤ amplitude ∧ ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, 0 < count → ∀ phase : Fin count → ℝ,
    ∃ witness : ReferenceMaterialCoarseWitness ⟨alpha, amplitude, ratio, frequency⟩ phase threshold constant,
      ReferenceSolution ⟨alpha, amplitude, ratio, frequency⟩
        witness.trajectory.movingFamily.patchMotion phase threshold constant := by
  obtain ⟨coarseRadius, coarsePositive, coarseSmall, coarseConstant, coarseConstantPositive, preparations⟩ :=
    exists_uniform_reference_material_coarse_preparation alphaPositive ratioLarge
  obtain ⟨sharpRadius, sharpPositive, sharpSmall, sharpConstant, sharpOne, sharpFactories⟩ :=
    exists_uniform_paper_reference_sharp_bounds
  obtain ⟨outerConstant, outerOne, outerFactories⟩ := exists_uniform_paper_reference_outer_displacement
  let thresholdMax := min coarseRadius sharpRadius
  let constant := max coarseConstant (max sharpConstant outerConstant)
  have coarseDominated : coarseConstant ≤ constant := le_max_left _ _
  have sharpDominated : sharpConstant ≤ constant := (le_max_left _ _).trans (le_max_right _ _)
  have outerDominated : outerConstant ≤ constant := (le_max_right _ _).trans (le_max_right _ _)
  have constantPositive : 0 < constant := coarseConstantPositive.trans_le coarseDominated
  refine ⟨thresholdMax, lt_min coarsePositive sharpPositive, ?_⟩
  intro threshold thresholdPositive thresholdBound
  have thresholdCoarse : threshold ≤ coarseRadius := thresholdBound.trans (min_le_left _ _)
  have thresholdSharp : threshold ≤ sharpRadius := thresholdBound.trans (min_le_right _ _)
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdCoarse.trans coarseSmall
  obtain ⟨amplitudeMin, amplitudeMinPositive, constantAmplitudeMin, preparation⟩ :=
    preparations threshold thresholdPositive thresholdCoarse constant coarseDominated
  refine ⟨amplitudeMin, amplitudeMinPositive, ?_⟩
  intro amplitude amplitudeLarge
  have amplitudePositive : 0 < amplitude := amplitudeMinPositive.trans_le amplitudeLarge
  have constantAmplitude : constant ≤ amplitude := constantAmplitudeMin.trans amplitudeLarge
  let scales : Scales := ⟨alpha, amplitude, ratio, 0⟩
  have eventual : ∀ᶠ frequency : ℝ in atTop,
      ∀ count : ℕ, 0 < count → ∀ phase : Fin count → ℝ,
      ∃ witness : ReferenceMaterialCoarseWitness ⟨alpha, amplitude, ratio, frequency⟩ phase threshold constant,
        ReferenceSolution ⟨alpha, amplitude, ratio, frequency⟩
          witness.trajectory.movingFamily.patchMotion phase threshold constant := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), preparation amplitude amplitudeLarge,
      sharpFactories scales amplitudePositive ratioLarge alphaPositive constant constantPositive.le constantAmplitude
        threshold thresholdSharp,
      outerFactories scales amplitudePositive ratioLarge alphaPositive thresholdSmall constantPositive.le constantAmplitude]
      with frequency frequencyLarge prepared sharpAll outerAll
    let changed : Scales := {scales with frequency := frequency}
    have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
    have ratioPositive : 0 < changed.ratio := by change 0 < ratio; linarith
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
        (pow_nonneg (changed.location_pos _).le _)
    have tailNonnegative : 0 ≤ ∑' source : ℕ, changed.circulation (source + 2) :=
      tsum_nonneg fun source => (changed.circulation_pos frequencyPositive ratioPositive _).le
    have omegaOnePositive := changed.omega_pos frequencyPositive ratioPositive 1
    have lengthOnePositive := changed.length_pos 1
    have outerBudgetNonnegative : 0 ≤ changed.outerDisplacementBound := by
      dsimp only [Scales.outerDisplacementBound]
      positivity
    have sharpResult {count : ℕ} (motion : PatchMotion count)
        {phase unstable : Fin count → ℝ} (phaseLift : ℝ → Fin count → ℝ)
        (initial : ReferenceInitialDisks changed motion phase unstable threshold)
        (givenLift : ReferencePhaseLift motion phase phaseLift)
        (evolution : FinitePatchEvolution changed motion 2)
        (coarse : ReferenceCoarseBounds changed motion threshold constant) :
        ReferenceSharpBounds changed motion phase phaseLift constant := by
      constructor
      · intro terminal terminalPositive terminalBound time member index
        have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
        have terminalNonnegative := terminalPositive.le
        have actual := sharpAll motion evolution phaseLift initial givenLift coarse terminal terminalPositive terminalBound time member index
        constructor
        · exact actual.1.trans (mul_le_mul_of_nonneg_right sharpDominated (by positivity))
        · exact actual.2.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right sharpDominated terminalNonnegative) (by positivity))
      · intro time member index outer
        exact (outerAll motion evolution initial coarse time member index outer).trans
          (mul_le_mul_of_nonneg_right outerDominated outerBudgetNonnegative)
    intro count countPositive phase
    obtain ⟨witness, phaseLift, lift⟩ := prepared count countPositive phase
    exact ⟨witness, witness.unstable, phaseLift, witness.initial, lift, witness.evolution, witness.coarse,
      sharpResult witness.trajectory.movingFamily.patchMotion phaseLift witness.initial lift witness.evolution witness.coarse⟩
  exact ⟨constant, constantPositive, constantAmplitude, eventual⟩

end EulerNonuniqueness.Paper

