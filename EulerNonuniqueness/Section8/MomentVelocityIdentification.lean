import EulerNonuniqueness.Section8.MomentVelocityPath
import EulerNonuniqueness.Section8.BiotSavartInjectivity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem MomentCompactnessData.exists_datum_of_velocityLp_tendsto
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) {velocityLimit : Lp Plane 2 (volume : Measure Plane)}
    (converges : Tendsto (fun index => data.velocityLp (parameters index).1 (parameters index).2) atTop (𝓝 velocityLimit)) :
    ∃ limit : Vorticity, ∃ datum : InitialDatum limit, datum.velocityLp = velocityLimit ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ test : Vorticity,
        MemLp test 2 volume → Tendsto
          (fun index => ∫ position, sequence (parameters (subsequence index)).1
            (parameters (subsequence index)).2 position * test position)
          atTop (𝓝 (∫ position, limit position * test position)) := by
  obtain ⟨limit, datum, subsequence, increasing, weak, velocityConverges⟩ :=
    data.exists_joint_vorticity_velocity_subsequence parameters
  let members : ∀ index, MemLp
      (biotSavart (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2))
      2 volume := fun index => data.biotSavart_memLp_two
        (parameters (subsequence index)).1 (parameters (subsequence index)).2.property
  have actualConverges : Tendsto
      (fun index => data.velocityLp (parameters (subsequence index)).1 (parameters (subsequence index)).2)
      atTop (𝓝 datum.velocityLp) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ members _ datum.biotSavart_memLp_two).mpr velocityConverges
  have sameLimit : datum.velocityLp = velocityLimit :=
    tendsto_nhds_unique actualConverges (converges.comp increasing.tendsto_atTop)
  exact ⟨limit, datum, sameLimit, subsequence, increasing, weak⟩

theorem MomentCompactnessData.weakL2_of_velocityLp_tendsto
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) {limit : Vorticity} (datum : InitialDatum limit)
    (converges : Tendsto (fun index => data.velocityLp (parameters index).1 (parameters index).2)
      atTop (𝓝 datum.velocityLp)) :
    ∀ test : Vorticity, MemLp test 2 volume → Tendsto
      (fun index => ∫ position, sequence (parameters index).1 (parameters index).2 position * test position)
      atTop (𝓝 (∫ position, limit position * test position)) := by
  intro test testMember
  apply tendsto_of_subseq_tendsto
  intro sampling samplingTends
  obtain ⟨candidate, candidateDatum, equality, extraction, _, weak⟩ :=
    data.exists_datum_of_velocityLp_tendsto (parameters ∘ sampling) (converges.comp samplingTends)
  have almostEverywhere : candidate =ᵐ[volume] limit := candidateDatum.ae_eq_of_velocityLp_eq datum equality
  have integralEquality : (∫ position, candidate position * test position) =
      ∫ position, limit position * test position := by
    apply integral_congr_ae
    filter_upwards [almostEverywhere] with position equality
    rw [equality]
  refine ⟨extraction, ?_⟩
  simpa only [Function.comp_def, integralEquality] using weak test testMember

end EulerNonuniqueness
