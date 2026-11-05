import EulerNonuniqueness.Section3.MovingStrainAffineTaylorIdentity
import EulerNonuniqueness.Section3.MovingStrainPrimitiveFormula
import EulerNonuniqueness.Section3.MovingStrainRealBaseBounds
import EulerNonuniqueness.Section3.DiskRotatingPhysicalRelativeTaylor
import EulerNonuniqueness.Section3.DiskRotatingDerivativeRelativeIncrement
import EulerNonuniqueness.Section3.DiskRotatingUniformTaylor
import EulerNonuniqueness.General.AffineTaylorRelativeQuadratic
import EulerNonuniqueness.Section3.MovingStrainAffineTaylorValue

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

theorem movingStrainAffineTaylorRemainder_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      contourCentroidFunctional (initialBase + initialIncrement) = contourCentroidFunctional initialBase →
      contourCentroidFunctional (finalBase + finalIncrement) = contourCentroidFunctional finalBase →
      ∀ coefficient : ℂ,
      ‖movingStrainAffineTaylorRemainder initialBase coefficient initialIncrement -
        movingStrainAffineTaylorRemainder finalBase coefficient finalIncrement‖ ≤ constant * ‖coefficient‖ *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2) := by
  obtain ⟨sourceRadius, sourcePositive, sourceConstant, sourceBound⟩ :=
    projectedComplexStrainTaylorRemainder_exists_relative_quadratic_ball
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeBound⟩ :=
    diskRotatingDerivativeTaylorRemainder_exists_relative_quadratic_ball
  obtain ⟨taylorRadius, taylorPositive, taylorConstant, taylorBound⟩ :=
    diskRotatingTaylorRemainder_exists_relative_quadratic_ball
  obtain ⟨generatorRadius, generatorPositive, generatorConstant, generatorNonnegative, generatorBound⟩ :=
    diskEulerRotatingField_derivative_exists_relative_increment_ball
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionBound, correctionDifference⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_base_bounds
  obtain ⟨rawRadius, rawPositive, _, rawConstant, rawOne, rawBound⟩ :=
    diskEulerRotatingField_exists_uniform_firstJet_bounds
  let radius := min (min sourceRadius derivativeRadius)
    (min (min taylorRadius generatorRadius) (min correctionRadius (min rawRadius 1)))
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have sourceLe : radius ≤ sourceRadius := (min_le_left _ _).trans (min_le_left _ _)
  have derivativeLe : radius ≤ derivativeRadius := (min_le_left _ _).trans (min_le_right _ _)
  have taylorLe : radius ≤ taylorRadius := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have generatorLe : radius ≤ generatorRadius := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have correctionLe : radius ≤ correctionRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have rawLe : radius ≤ rawRadius := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have radiusOne : radius ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let derivativeCoefficient := rawConstant + (derivativeConstant : ℝ)
  let taylorCoefficient := rawConstant + (taylorConstant : ℝ)
  let constant := (sourceConstant : ℝ) + 8 * derivativeCoefficient +
    2 * generatorConstant * correctionConstant + 2 * correctionConstant * taylorCoefficient
  have rawNonnegative : 0 ≤ rawConstant := by linarith
  have correctionNonnegative : 0 ≤ correctionConstant := by linarith
  have derivativeNonnegative : 0 ≤ derivativeCoefficient := by dsimp [derivativeCoefficient]; positivity
  have taylorNonnegative : 0 ≤ taylorCoefficient := by dsimp [taylorCoefficient]; positivity
  refine ⟨radius, radiusPositive, constant, by dsimp [constant]; positivity, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside initialCentroid finalCentroid coefficient
  let size := ‖initialIncrement‖ + ‖finalIncrement‖
  let budget := size * ‖initialIncrement - finalIncrement‖ + ‖initialBase - finalBase‖ * size ^ 2
  have sizeNonnegative : 0 ≤ size := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have budgetNonnegative : 0 ≤ budget := add_nonneg
    (mul_nonneg sizeNonnegative (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have finalSize : ‖finalIncrement‖ ≤ size := le_add_of_nonneg_left (norm_nonneg initialIncrement)
  have squareBound : ‖finalIncrement‖ ^ 2 ≤ size ^ 2 := pow_le_pow_left₀ (norm_nonneg _) finalSize 2
  have weakBudget : size * ‖initialIncrement - finalIncrement‖ +
      ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2 ≤ budget :=
    add_le_add_left (mul_le_mul_of_nonneg_left squareBound (norm_nonneg _)) _
  have initialBaseBound : ‖initialBase - standardCircleBanach‖ ≤ radius := by
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have finalBaseBound : ‖finalBase - standardCircleBanach‖ ≤ radius := by
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have initialSingle : ‖initialBase - standardCircleBanach‖ + ‖initialIncrement‖ ≤ radius := by
    linarith [norm_nonneg finalIncrement]
  have finalSingle : ‖finalBase - standardCircleBanach‖ + ‖finalIncrement‖ ≤ radius := by
    linarith [norm_nonneg initialIncrement]
  have sourceActual := sourceBound initialBase finalBase initialIncrement finalIncrement
    (initialInside.trans sourceLe) (finalInside.trans sourceLe) initialCentroid finalCentroid coefficient
  have sourceEstimate : ‖projectedComplexStrainTaylorRemainder initialBase coefficient initialIncrement -
      projectedComplexStrainTaylorRemainder finalBase coefficient finalIncrement‖ ≤
      (sourceConstant : ℝ) * ‖coefficient‖ * budget := by
    have enlarged := sourceActual.trans (mul_le_mul_of_nonneg_left weakBudget (by positivity : 0 ≤ ‖coefficient‖ * sourceConstant))
    convert enlarged using 1 <;> ring
  have derivativeActual := derivativeBound initialBase finalBase initialIncrement finalIncrement
    (initialInside.trans derivativeLe) (finalInside.trans derivativeLe)
  have derivativeEstimate : ‖diskRotatingDerivativeTaylorRemainder initialBase initialIncrement -
      diskRotatingDerivativeTaylorRemainder finalBase finalIncrement‖ ≤ derivativeCoefficient * budget :=
    derivativeActual.trans (mul_le_mul (by dsimp [derivativeCoefficient]; linarith)
      weakBudget (by positivity) derivativeNonnegative)
  have taylorActual := taylorBound initialBase finalBase initialIncrement finalIncrement
    (initialInside.trans taylorLe) (finalInside.trans taylorLe)
  have taylorEstimate : ‖diskRotatingTaylorRemainder initialBase initialIncrement -
      diskRotatingTaylorRemainder finalBase finalIncrement‖ ≤ taylorCoefficient * budget :=
    taylorActual.trans (mul_le_mul (by dsimp [taylorCoefficient]; linarith)
      weakBudget (by positivity) taylorNonnegative)
  have rawInitial := rawBound initialBase initialIncrement (initialSingle.trans rawLe)
  have rawFinal := rawBound finalBase finalIncrement (finalSingle.trans rawLe)
  have derivativeAbsolute : ‖diskRotatingDerivativeTaylorRemainder initialBase initialIncrement‖ ≤
      derivativeCoefficient * ‖initialIncrement‖ ^ 2 :=
    rawInitial.2.2.2.trans (mul_le_mul_of_nonneg_right
      (by dsimp [derivativeCoefficient]; linarith [derivativeConstant.coe_nonneg]) (sq_nonneg _))
  have taylorAbsolute : ‖diskRotatingTaylorRemainder finalBase finalIncrement‖ ≤
      taylorCoefficient * ‖finalIncrement‖ ^ 2 :=
    rawFinal.2.2.1.trans (mul_le_mul_of_nonneg_right
      (by dsimp [taylorCoefficient]; linarith [taylorConstant.coe_nonneg]) (sq_nonneg _))
  have generatorRelative := generatorBound initialBase finalBase initialIncrement finalIncrement
    (initialInside.trans generatorLe) (finalInside.trans generatorLe)
  have initialZero : ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖(0 : PeriodicC1HolderHalf)‖) ≤
      generatorRadius := by simpa only [norm_zero, add_zero] using initialSingle.trans generatorLe
  have generatorAbsolute := generatorBound initialBase initialBase initialIncrement 0 initialZero initialZero
  simp only [add_zero, sub_self, sub_zero, norm_zero, zero_mul, mul_zero] at generatorAbsolute
  have correctionInitial := correctionBound initialBase (initialBaseBound.trans correctionLe) coefficient
  have correctionFinal := correctionBound finalBase (finalBaseBound.trans correctionLe) coefficient
  have correctionRelative := correctionDifference initialBase finalBase
    (initialBaseBound.trans correctionLe) (finalBaseBound.trans correctionLe) coefficient
  have finalNorm : ‖finalBase‖ ≤ 3 := by
    have triangle : ‖finalBase‖ ≤ ‖finalBase - standardCircleBanach‖ + ‖standardCircleBanach‖ := by
      simpa only [sub_add_cancel] using norm_add_le (finalBase - standardCircleBanach) standardCircleBanach
    linarith [finalBaseBound.trans radiusOne, standardCircleBanach_norm_bound]
  have primitiveAbsolute : ‖movingStrainRealPrimitiveValue finalBase coefficient‖ ≤ 6 * ‖coefficient‖ := by
    have actual := (movingStrainRealPrimitiveValue_norm_bound finalBase coefficient).trans
      (mul_le_mul_of_nonneg_left finalNorm (by positivity : 0 ≤ 2 * ‖coefficient‖))
    convert actual using 1 <;> ring
  have primitiveRelative := movingStrainRealPrimitiveValue_difference_bound initialBase finalBase coefficient
  have vectorBound := EulerNonuniqueness.General.affine_taylor_relative_quadratic_bound
    (projectedComplexStrainTaylorRemainder initialBase coefficient initialIncrement)
    (projectedComplexStrainTaylorRemainder finalBase coefficient finalIncrement)
    (movingStrainRealPrimitiveValue initialBase coefficient) (movingStrainRealPrimitiveValue finalBase coefficient)
    initialIncrement finalIncrement (diskRotatingTaylorRemainder initialBase initialIncrement)
    (diskRotatingTaylorRemainder finalBase finalIncrement)
    (diskRotatingDerivativeTaylorRemainder initialBase initialIncrement)
    (diskRotatingDerivativeTaylorRemainder finalBase finalIncrement)
    (fderiv ℝ diskEulerRotatingField (initialBase + initialIncrement) - fderiv ℝ diskEulerRotatingField initialBase)
    (fderiv ℝ diskEulerRotatingField (finalBase + finalIncrement) - fderiv ℝ diskEulerRotatingField finalBase)
    (movingStrainRealCorrectionCLM initialBase coefficient) (movingStrainRealCorrectionCLM finalBase coefficient)
    sourceConstant.coe_nonneg derivativeNonnegative generatorNonnegative correctionNonnegative
    taylorNonnegative (norm_nonneg coefficient) (norm_nonneg (initialBase - finalBase)) (le_refl size)
    sourceEstimate derivativeAbsolute derivativeEstimate primitiveAbsolute primitiveRelative
    generatorAbsolute generatorRelative correctionInitial correctionFinal correctionRelative taylorEstimate taylorAbsolute
  rw [movingStrainAffineTaylorRemainder_eq_named_jets initialBase coefficient initialIncrement,
    movingStrainAffineTaylorRemainder_eq_named_jets finalBase coefficient finalIncrement]
  have scalarEquality : ‖coefficient‖ * constant * budget = constant * ‖coefficient‖ * budget := by ring
  exact vectorBound.trans_eq scalarEquality

end EulerNonuniqueness.Paper
