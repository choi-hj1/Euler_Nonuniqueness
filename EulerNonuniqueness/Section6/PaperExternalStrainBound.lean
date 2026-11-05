import EulerNonuniqueness.Section6.PaperExternalStrainGeometry
import EulerNonuniqueness.Section6.PaperForeignTransportBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.norm_externalQuadrupoleStrainDerivative_le
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count)
    (receiverBounded : ∀ patch, motion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter motion time index) radius)
    (receiverSmall : 2 * radius ≤ scales.location (index.val + 1) / 24)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain time source patch →
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤
          ‖quadrupoleCenter motion time index - position‖) :
    ‖externalQuadrupoleStrainDerivative scales motion index time‖ ≤
      (55296 / Real.pi) * scales.strain *
        ‖((∑ patch : Fin 4, patchAverageVelocity scales motion time index patch
            (biotSavart (patchVorticity scales motion time))) / 4) -
          biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index)‖ /
        scales.location (index.val + 1) + (34504704 / Real.pi ^ 2) * scales.strain ^ 2 := by
  have actual := evolution.foreign_material_transport_le_strain inside amplitudePositive frequencyBound
    ratioBound alphaPositive index (quadrupoleCenter motion time index)
    ((∑ patch : Fin 4, patchAverageVelocity scales motion time index patch
      (biotSavart (patchVorticity scales motion time))) / 4) receiverBounded receiverSmall separated
  have factor : ‖Complex.I / (Real.pi : ℂ)‖ = 1 / Real.pi := by
    simp only [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [externalQuadrupoleStrainDerivative, norm_mul, factor]
  apply (mul_le_mul_of_nonneg_left actual (by positivity : 0 ≤ 1 / Real.pi)).trans_eq
  ring

end EulerNonuniqueness.Paper
