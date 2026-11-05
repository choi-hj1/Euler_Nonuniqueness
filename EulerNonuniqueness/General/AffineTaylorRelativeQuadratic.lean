import EulerNonuniqueness.General.AffineResidualRelativeRemainder
import EulerNonuniqueness.General.PairedAffineRemainderBudget

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem affine_taylor_relative_quadratic_bound
    (sourceInitial sourceFinal primitiveInitial primitiveFinal initial final selfInitial selfFinal : Space)
    (derivativeInitial derivativeFinal generatorInitial generatorFinal correctionInitial correctionFinal : Space →L[ℝ] Space)
    {sourceConstant derivativeConstant generatorConstant correctionConstant taylorConstant amplitude baseDifference size : ℝ}
    (sourceNonnegative : 0 ≤ sourceConstant) (derivativeNonnegative : 0 ≤ derivativeConstant)
    (generatorNonnegative : 0 ≤ generatorConstant) (correctionNonnegative : 0 ≤ correctionConstant)
    (taylorNonnegative : 0 ≤ taylorConstant) (amplitudeNonnegative : 0 ≤ amplitude)
    (baseNonnegative : 0 ≤ baseDifference) (sizeBound : ‖initial‖ + ‖final‖ ≤ size)
    (sourceBound : ‖sourceInitial - sourceFinal‖ ≤ sourceConstant * amplitude *
      (size * ‖initial - final‖ + baseDifference * size ^ 2))
    (derivativeAbsolute : ‖derivativeInitial‖ ≤ derivativeConstant * ‖initial‖ ^ 2)
    (derivativeRelative : ‖derivativeInitial - derivativeFinal‖ ≤ derivativeConstant *
      (size * ‖initial - final‖ + baseDifference * size ^ 2))
    (primitiveAbsolute : ‖primitiveFinal‖ ≤ 6 * amplitude)
    (primitiveRelative : ‖primitiveInitial - primitiveFinal‖ ≤ 2 * amplitude * baseDifference)
    (generatorAbsolute : ‖generatorInitial‖ ≤ generatorConstant * ‖initial‖)
    (generatorRelative : ‖generatorInitial - generatorFinal‖ ≤ generatorConstant *
      (‖initial - final‖ + baseDifference * ‖final‖))
    (correctionAbsolute : ‖correctionInitial‖ ≤ correctionConstant * amplitude)
    (correctionFinalBound : ‖correctionFinal‖ ≤ correctionConstant * amplitude)
    (correctionRelative : ‖correctionInitial - correctionFinal‖ ≤ correctionConstant * amplitude * baseDifference)
    (selfRelative : ‖selfInitial - selfFinal‖ ≤ taylorConstant *
      (size * ‖initial - final‖ + baseDifference * size ^ 2))
    (selfAbsolute : ‖selfFinal‖ ≤ taylorConstant * ‖final‖ ^ 2) :
    ‖(sourceInitial + derivativeInitial primitiveInitial + generatorInitial (correctionInitial initial) -
        correctionInitial selfInitial) -
      (sourceFinal + derivativeFinal primitiveFinal + generatorFinal (correctionFinal final) -
        correctionFinal selfFinal)‖ ≤ amplitude *
      (sourceConstant + 8 * derivativeConstant + 2 * generatorConstant * correctionConstant +
        2 * correctionConstant * taylorConstant) *
      (size * ‖initial - final‖ + baseDifference * size ^ 2) := by
  have sizeNonnegative := (add_nonneg (norm_nonneg initial) (norm_nonneg final)).trans sizeBound
  have derivativeTerm :
      ‖derivativeInitial‖ * ‖primitiveInitial - primitiveFinal‖ +
        ‖derivativeInitial - derivativeFinal‖ * ‖primitiveFinal‖ ≤
      derivativeConstant * ‖initial‖ ^ 2 * (2 * amplitude * baseDifference) +
        derivativeConstant * (size * ‖initial - final‖ + baseDifference * size ^ 2) * (6 * amplitude) := by
    gcongr
  have generatorTerm :
      ‖generatorInitial‖ * (‖correctionInitial‖ * ‖initial - final‖ +
        ‖correctionInitial - correctionFinal‖ * ‖final‖) +
        ‖generatorInitial - generatorFinal‖ * (‖correctionFinal‖ * ‖final‖) ≤
      generatorConstant * ‖initial‖ * (correctionConstant * amplitude * ‖initial - final‖ +
        correctionConstant * amplitude * baseDifference * ‖final‖) +
        generatorConstant * (‖initial - final‖ + baseDifference * ‖final‖) *
          (correctionConstant * amplitude * ‖final‖) := by
    gcongr
  have selfTerm :
      ‖correctionInitial‖ * ‖selfInitial - selfFinal‖ + ‖correctionInitial - correctionFinal‖ * ‖selfFinal‖ ≤
      correctionConstant * amplitude * taylorConstant * (size * ‖initial - final‖ + baseDifference * size ^ 2) +
        correctionConstant * amplitude * baseDifference * taylorConstant * ‖final‖ ^ 2 := by
    calc
      _ ≤ (correctionConstant * amplitude) *
            (taylorConstant * (size * ‖initial - final‖ + baseDifference * size ^ 2)) +
          (correctionConstant * amplitude * baseDifference) * (taylorConstant * ‖final‖ ^ 2) := by gcongr
      _ = _ := by ring
  have vectorBound := affineResidual_quadratic_remainder_difference_bound sourceInitial sourceFinal
    primitiveInitial primitiveFinal initial final selfInitial selfFinal derivativeInitial derivativeFinal
    generatorInitial generatorFinal correctionInitial correctionFinal
  have enlarged := vectorBound.trans (add_le_add (add_le_add (add_le_add sourceBound derivativeTerm) generatorTerm) selfTerm)
  exact enlarged.trans (paired_affine_remainder_scalar_budget
    (norm_nonneg initial) (norm_nonneg final) (norm_nonneg (initial - final)) baseNonnegative
    amplitudeNonnegative sourceNonnegative derivativeNonnegative generatorNonnegative
    correctionNonnegative taylorNonnegative sizeBound)

end EulerNonuniqueness.General
