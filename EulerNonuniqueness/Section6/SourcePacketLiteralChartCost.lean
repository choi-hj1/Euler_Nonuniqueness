import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison
import EulerNonuniqueness.Section6.SourcePacketActualPhaseCost

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

namespace SourcePacketPhysicalGeometry

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

def sourceCost (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (elapsed : ℝ) : ℝ :=
  4 * (4096 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * geometry.deformation /
      (Real.pi * geometry.gap ^ 4) +
    (4 * scales.circulation (source.val + 1) * ‖centroidAsymmetry family.patchMotion (start + elapsed) source‖ /
        (Real.pi * geometry.observationDistance ^ 3) +
      3 * (‖(∫ position, quadrupoleDensity scales family.patchMotion (start + elapsed) source position •
          (position - quadrupoleCenter family.patchMotion (start + elapsed) source) ^ 2) - geometry.targetMoment elapsed‖ +
        512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * geometry.deformation) /
        (2 * Real.pi * geometry.observationDistance ^ 4) +
      352 * scales.circulation (source.val + 1) * geometry.pairRadius ^ 2 * geometry.halfWidth /
        (Real.pi * geometry.observationDistance ^ 5))) +
  768 * ‖geometry.targetMoment elapsed‖ *
    ‖(geometry.location elapsed - (geometry.firstCenter elapsed + geometry.secondCenter elapsed) / 2) -
      geometry.frozenDisplacement‖ / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 5)

theorem literal_source_error_bound (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {elapsed : ℝ} (inside : elapsed ∈ Icc 0 horizon) :
    4 * ‖geometry.actualStrain elapsed - geometry.modelStrain elapsed‖ ≤ geometry.sourceCost elapsed := by
  have spatial := geometry.evolution.quadrupole_uniform_paired_strain_error (geometry.timeRange elapsed inside)
    geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive source (geometry.location elapsed)
    (geometry.firstCenter elapsed) (geometry.secondCenter elapsed) (geometry.firstSeparation elapsed)
    (geometry.secondSeparation elapsed) (geometry.targetMoment elapsed) (geometry.positions elapsed inside)
    (geometry.control elapsed inside) geometry.deformationNonnegative geometry.deformationSmall geometry.gapPositive
    geometry.radiusSmall (geometry.separated elapsed inside) geometry.widthPositive (geometry.firstBound elapsed inside)
    (geometry.secondBound elapsed inside) (geometry.pairSeparated elapsed inside) (geometry.far elapsed inside)
    geometry.observationPositive (geometry.observationLower elapsed inside) (geometry.pairUpper elapsed inside)
  have translation := physical_second_moment_strain_translation_bound (geometry.targetMoment elapsed)
    geometry.frozenNonzero (geometry.displacementClose elapsed inside)
  have total := (norm_sub_le_norm_sub_add_norm_sub (geometry.actualStrain elapsed)
    (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star
      (3 * geometry.targetMoment elapsed / (geometry.location elapsed - (geometry.firstCenter elapsed + geometry.secondCenter elapsed) / 2) ^ 4))
    (geometry.modelStrain elapsed)).trans (add_le_add spatial translation)
  have multiplied := mul_le_mul_of_nonneg_left total (by norm_num : (0 : ℝ) ≤ 4)
  convert multiplied using 1 <;> dsimp only [sourceCost] <;> ring

theorem actual_strain_le_literal_cost (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {elapsed : ℝ} (inside : elapsed ∈ Icc 0 horizon) :
    4 * ‖geometry.actualStrain elapsed‖ ≤
      (6 / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4)) * ‖geometry.targetMoment elapsed‖ + geometry.sourceCost elapsed := by
  have triangle := norm_add_le (geometry.actualStrain elapsed - geometry.modelStrain elapsed) (geometry.modelStrain elapsed)
  rw [sub_add_cancel] at triangle
  have bound := geometry.literal_source_error_bound inside
  have identity := source_packet_model_strain_norm (geometry.targetMoment elapsed) geometry.frozenDisplacement
  change 4 * ‖geometry.modelStrain elapsed‖ = _ at identity
  nlinarith

theorem chart_cost_le_literal_cost (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {elapsed constant chartBound : ℝ} (inside : elapsed ∈ Icc 0 horizon) (constantNonnegative : 0 ≤ constant)
    (chartSmall : |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
      |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2| ≤ chartBound) :
    constant * ‖geometry.actualStrain elapsed‖ *
        (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
          |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|) ≤
      (constant * chartBound / 4) *
        ((6 / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4)) * ‖geometry.targetMoment elapsed‖ + geometry.sourceCost elapsed) := by
  have chartNonnegative : 0 ≤ chartBound :=
    (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans chartSmall
  have chart := mul_le_mul_of_nonneg_left chartSmall
    (mul_nonneg constantNonnegative (norm_nonneg (geometry.actualStrain elapsed)))
  have literal := mul_le_mul_of_nonneg_left (geometry.actual_strain_le_literal_cost inside)
    (show 0 ≤ constant * chartBound / 4 by positivity)
  nlinarith

end SourcePacketPhysicalGeometry

end EulerNonuniqueness.Paper
