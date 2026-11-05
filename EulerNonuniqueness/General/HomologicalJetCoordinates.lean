import EulerNonuniqueness.General.BilinearOperatorCalculus
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def coordinateLinearJet (chart : Space ≃L[ℝ] Space) (chartSecond : BilinearEnd Space)
    (value : Space) (linear : Space →L[ℝ] Space) (direction : Space) : Space :=
  chart.symm (linear (chart direction) - chartSecond direction (chart.symm value))

def coordinateQuadraticJet (chart : Space ≃L[ℝ] Space) (chartSecond : BilinearEnd Space)
    (linear : Space →L[ℝ] Space) (second : BilinearEnd Space) (first secondDirection : Space) : Space :=
  chart.symm (second (chart first) (chart secondDirection) + linear (chartSecond first secondDirection) -
    chartSecond first (chart.symm (linear (chart secondDirection))) -
    chartSecond secondDirection (chart.symm (linear (chart first))))

theorem homological_jet_coordinate_identity
    (chart : Space ≃L[ℝ] Space) (chartSecond : BilinearEnd Space)
    (symmetric : ∀ first second, chartSecond first second = chartSecond second first)
    (generator sourceLinear correctionLinear partnerLinear : Space →L[ℝ] Space)
    (generatorSecond : BilinearEnd Space) (sourceValue correctionValue partnerValue direction : Space)
    (frequency : ℝ) :
    coordinateLinearJet chart chartSecond sourceValue sourceLinear direction +
        coordinateQuadraticJet chart chartSecond generator generatorSecond direction (chart.symm correctionValue) +
        chart.symm (generator (chart (coordinateLinearJet chart chartSecond correctionValue correctionLinear direction))) -
        coordinateLinearJet chart chartSecond correctionValue correctionLinear
          (chart.symm (generator (chart direction))) -
        frequency • coordinateLinearJet chart chartSecond partnerValue partnerLinear direction =
      chart.symm (sourceLinear (chart direction) + generatorSecond (chart direction) correctionValue +
        generator (correctionLinear (chart direction)) - correctionLinear (generator (chart direction)) -
        frequency • partnerLinear (chart direction) -
        chartSecond direction (chart.symm (sourceValue + generator correctionValue - frequency • partnerValue))) := by
  unfold coordinateLinearJet coordinateQuadraticJet
  apply chart.injective
  simp only [map_add, map_sub, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [symmetric (chart.symm correctionValue) (chart.symm (generator (chart direction)))]
  simp only [smul_sub]
  abel

theorem homological_jet_coordinate_equation
    (chart : Space ≃L[ℝ] Space) (chartSecond : BilinearEnd Space)
    (symmetric : ∀ first second, chartSecond first second = chartSecond second first)
    (generator sourceLinear correctionLinear partnerLinear : Space →L[ℝ] Space)
    (generatorSecond : BilinearEnd Space) (sourceValue correctionValue partnerValue direction : Space)
    (frequency : ℝ)
    (valueEquation : sourceValue + generator correctionValue - frequency • partnerValue = 0)
    (linearEquation : sourceLinear (chart direction) + generatorSecond (chart direction) correctionValue +
      generator (correctionLinear (chart direction)) - correctionLinear (generator (chart direction)) -
      frequency • partnerLinear (chart direction) = 0) :
    coordinateLinearJet chart chartSecond sourceValue sourceLinear direction +
        coordinateQuadraticJet chart chartSecond generator generatorSecond direction (chart.symm correctionValue) +
        chart.symm (generator (chart (coordinateLinearJet chart chartSecond correctionValue correctionLinear direction))) -
        coordinateLinearJet chart chartSecond correctionValue correctionLinear
          (chart.symm (generator (chart direction))) -
        frequency • coordinateLinearJet chart chartSecond partnerValue partnerLinear direction = 0 := by
  rw [homological_jet_coordinate_identity chart chartSecond symmetric generator sourceLinear correctionLinear
    partnerLinear generatorSecond sourceValue correctionValue partnerValue direction frequency,
    valueEquation, linearEquation, map_zero, map_zero, sub_zero, map_zero]

end EulerNonuniqueness.General
