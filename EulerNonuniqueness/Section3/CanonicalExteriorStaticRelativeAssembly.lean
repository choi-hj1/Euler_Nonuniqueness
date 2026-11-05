import EulerNonuniqueness.Section3.MovingStrainAffineAmplitudeRelative
import EulerNonuniqueness.Section3.DiskRotatingRelativeShiftError
import EulerNonuniqueness.Section3.ProjectedExteriorSeriesRelativeIncrement
import EulerNonuniqueness.Section3.DiskRotatingRelativePrimitiveError
import EulerNonuniqueness.Section3.MovingStrainExteriorProductRelative
import EulerNonuniqueness.Section3.ExteriorSeriesLeadingMode
import EulerNonuniqueness.General.FiveTermNormBound

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  powerFirstJetOperatorGroup exteriorPowerSeriesOperatorSpace gaugeOperatorUniformSecondGroup

def canonicalExteriorStaticResidual (phase : Circle) (frequency : ℝ) (coefficient : ℕ → ℂ)
    (base increment displacement primitive : PeriodicC1HolderHalf) (strain : ℂ) : PeriodicC1HolderHalf :=
  frequency • diskRotatingShiftError (base + increment) displacement +
    movingStrainAffineResidual base strain (base + increment) +
    (circleBasedProjectedExteriorSeries phase (exteriorCoefficientWithoutLeading coefficient)
        (base - standardCircleBanach + increment) -
      circleBasedProjectedExteriorSeries phase (exteriorCoefficientWithoutLeading coefficient)
        (base - standardCircleBanach)) +
    frequency • ((fderiv ℝ diskEulerRotatingField (base + increment) -
      fderiv ℝ diskEulerRotatingField base) primitive) -
    frequency⁻¹ • (movingStrainRealCorrectionCLM base strain
      (circleBasedProjectedExteriorSeries phase coefficient (base - standardCircleBanach + increment)))

def canonicalExteriorStaticRelativeBudget (frequency : ℝ) (initialCoefficient finalCoefficient : ℕ → ℂ)
    (firstBase finalBase firstIncrement finalIncrement firstShift finalShift firstPrimitive finalPrimitive : PeriodicC1HolderHalf)
    (initialStrain finalStrain : ℂ) : ℝ :=
  |frequency| * ((‖firstShift‖ + ‖finalShift‖) * ‖firstShift - finalShift‖ +
    ‖(firstBase + firstIncrement) - (finalBase + finalIncrement)‖ * ‖finalShift‖ ^ 2) +
  (‖initialStrain‖ * ((‖firstIncrement‖ + ‖finalIncrement‖) * ‖firstIncrement - finalIncrement‖ +
    ‖firstBase - finalBase‖ * (‖firstIncrement‖ + ‖finalIncrement‖) ^ 2) +
    ‖initialStrain - finalStrain‖ * ‖finalIncrement‖ ^ 2) +
  ((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖exteriorCoefficientWithoutLeading initialCoefficient degree‖) *
      (‖firstIncrement - finalIncrement‖ + ‖firstBase - finalBase‖ * ‖finalIncrement‖) +
    (∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖exteriorCoefficientWithoutLeading initialCoefficient degree - exteriorCoefficientWithoutLeading finalCoefficient degree‖) *
      ‖finalIncrement‖) +
  |frequency| * (‖firstIncrement‖ * ‖firstPrimitive - finalPrimitive‖ +
    (‖firstIncrement - finalIncrement‖ + ‖firstBase - finalBase‖ * ‖finalIncrement‖) * ‖finalPrimitive‖) +
  |frequency|⁻¹ * (‖initialStrain‖ *
      (((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) +
          (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) *
        ‖(firstBase + firstIncrement) - (finalBase + finalIncrement)‖ +
        ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖) +
    (‖initialStrain‖ * ‖firstBase - finalBase‖ + ‖initialStrain - finalStrain‖) *
      (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖))

theorem canonicalExteriorStaticResidual_exists_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ initialAngular finalAngular : PeriodicC1HolderHalf,
      ∀ (initialSmall : ‖initialAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2),
      initialAngular ∈ contourContinuousVectorSubmodule → finalAngular ∈ contourContinuousVectorSubmodule →
      let firstBase := fixedRelabelEquivalence initialAngular initialSmall standardCircleBanach
      let finalBase := fixedRelabelEquivalence finalAngular finalSmall standardCircleBanach
      ‖firstBase - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ‖finalBase - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ∀ firstIncrement finalIncrement firstShift finalShift firstPrimitive finalPrimitive : PeriodicC1HolderHalf,
      firstIncrement ∈ contourContinuousVectorSubmodule → finalIncrement ∈ contourContinuousVectorSubmodule →
      ‖firstBase - standardCircleBanach‖ + (‖firstIncrement‖ + ‖finalIncrement‖) +
        (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖firstIncrement‖ + ‖finalIncrement‖) +
        (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      contourCentroidFunctional (firstBase + firstIncrement) = contourCentroidFunctional firstBase →
      contourCentroidFunctional (finalBase + finalIncrement) = contourCentroidFunctional finalBase →
      ∀ (phase : Circle) (frequency : ℝ) (initialCoefficient finalCoefficient : ℕ → ℂ),
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) →
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖) →
      ∀ initialStrain finalStrain : ℂ,
      ‖canonicalExteriorStaticResidual phase frequency initialCoefficient firstBase firstIncrement firstShift firstPrimitive initialStrain -
        canonicalExteriorStaticResidual phase frequency finalCoefficient finalBase finalIncrement finalShift finalPrimitive finalStrain‖ ≤
      constant * canonicalExteriorStaticRelativeBudget frequency initialCoefficient finalCoefficient
        firstBase finalBase firstIncrement finalIncrement firstShift finalShift firstPrimitive finalPrimitive initialStrain finalStrain := by
  obtain ⟨leadingRadius, leadingPositive, leadingConstant, leadingNonnegative, leading⟩ :=
    movingStrainAffineResidual_exists_amplitude_relative_quadratic_ball
  obtain ⟨shiftRadius, shiftPositive, shiftConstant, shiftNonnegative, shifts⟩ :=
    diskRotatingShiftError_exists_scaled_relative_ball
  obtain ⟨seriesRadius, seriesPositive, seriesConstant, seriesNonnegative, series⟩ :=
    circleBasedProjectedExteriorSeries_exists_pair_relative_increment_ball
  obtain ⟨primitiveRadius, primitivePositive, primitiveConstant, primitiveNonnegative, primitives⟩ :=
    diskRotatingGeneratorPrimitive_exists_scaled_relative_ball
  obtain ⟨productRadius, productPositive, productConstant, productNonnegative, products⟩ :=
    movingStrainExteriorProduct_exists_scaled_relative_ball
  let radius := min leadingRadius (min shiftRadius (min seriesRadius (min primitiveRadius productRadius)))
  let constant := leadingConstant + shiftConstant + seriesConstant + primitiveConstant + productConstant
  have leadingLe : radius ≤ leadingRadius := min_le_left _ _
  have shiftLe : radius ≤ shiftRadius := (min_le_right _ _).trans (min_le_left _ _)
  have seriesLe : radius ≤ seriesRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have primitiveLe : radius ≤ primitiveRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have productLe : radius ≤ productRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨radius, by dsimp [radius]; positivity, constant, by dsimp [constant]; positivity, ?_⟩
  intro initialAngular finalAngular initialSmall finalSmall initialMember finalMember firstBase finalBase
    firstNearby finalNearby firstIncrement finalIncrement firstShift finalShift firstPrimitive finalPrimitive
    firstMember finalIncrementMember firstInside finalInside firstCentered finalCentered phase frequency
    initialCoefficient finalCoefficient initialSummable finalSummable initialStrain finalStrain
  have firstJoint : ‖firstBase - standardCircleBanach‖ + (‖firstIncrement‖ + ‖finalIncrement‖) ≤ radius := by
    linarith [norm_nonneg firstShift, norm_nonneg finalShift]
  have finalJoint : ‖finalBase - standardCircleBanach‖ + (‖firstIncrement‖ + ‖finalIncrement‖) ≤ radius := by
    linarith [norm_nonneg firstShift, norm_nonneg finalShift]
  have firstShiftInside : ‖firstBase + firstIncrement - standardCircleBanach‖ + (‖firstShift‖ + ‖finalShift‖) ≤ shiftRadius := by
    have triangle : ‖firstBase + firstIncrement - standardCircleBanach‖ ≤
        ‖firstBase - standardCircleBanach‖ + ‖firstIncrement‖ := by
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (firstBase - standardCircleBanach) firstIncrement
    linarith [firstInside.trans shiftLe, norm_nonneg finalIncrement]
  have finalShiftInside : ‖finalBase + finalIncrement - standardCircleBanach‖ + (‖firstShift‖ + ‖finalShift‖) ≤ shiftRadius := by
    have triangle : ‖finalBase + finalIncrement - standardCircleBanach‖ ≤
        ‖finalBase - standardCircleBanach‖ + ‖finalIncrement‖ := by
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (finalBase - standardCircleBanach) finalIncrement
    linarith [finalInside.trans shiftLe, norm_nonneg firstIncrement]
  have lead := leading initialAngular finalAngular initialSmall finalSmall initialMember finalMember
    firstNearby finalNearby firstIncrement finalIncrement firstMember finalIncrementMember
    (firstJoint.trans leadingLe) (finalJoint.trans leadingLe) firstCentered finalCentered initialStrain finalStrain
  have shift := shifts (firstBase + firstIncrement) (finalBase + finalIncrement) firstShift finalShift
    firstShiftInside finalShiftInside frequency
  have tailInitialSummable := exteriorCoefficientWithoutLeading_weight_summable initialCoefficient
    (by norm_num : (0 : ℝ) ≤ 96) initialSummable
  have tailFinalSummable := exteriorCoefficientWithoutLeading_weight_summable finalCoefficient
    (by norm_num : (0 : ℝ) ≤ 96) finalSummable
  have tail := series phase (exteriorCoefficientWithoutLeading initialCoefficient)
    (exteriorCoefficientWithoutLeading finalCoefficient) tailInitialSummable tailFinalSummable
    (firstBase - standardCircleBanach) (finalBase - standardCircleBanach) firstIncrement finalIncrement
    (firstJoint.trans seriesLe) (finalJoint.trans seriesLe)
  have baseDifference : (firstBase - standardCircleBanach) - (finalBase - standardCircleBanach) = firstBase - finalBase := by abel
  rw [baseDifference] at tail
  have primitive := primitives firstBase finalBase firstIncrement finalIncrement
    (firstJoint.trans primitiveLe) (finalJoint.trans primitiveLe) firstPrimitive finalPrimitive frequency
  have firstBaseInside : ‖firstBase - standardCircleBanach‖ ≤ productRadius := by
    linarith [firstJoint.trans productLe, norm_nonneg firstIncrement, norm_nonneg finalIncrement]
  have finalBaseInside : ‖finalBase - standardCircleBanach‖ ≤ productRadius := by
    linarith [finalJoint.trans productLe, norm_nonneg firstIncrement, norm_nonneg finalIncrement]
  have firstDataInside : ‖firstBase - standardCircleBanach + firstIncrement‖ ≤ productRadius :=
    (norm_add_le _ _).trans (by linarith [firstJoint.trans productLe, norm_nonneg finalIncrement])
  have finalDataInside : ‖finalBase - standardCircleBanach + finalIncrement‖ ≤ productRadius :=
    (norm_add_le _ _).trans (by linarith [finalJoint.trans productLe, norm_nonneg firstIncrement])
  have product := products phase initialCoefficient finalCoefficient initialSummable finalSummable firstBase finalBase
    (firstBase - standardCircleBanach + firstIncrement) (finalBase - standardCircleBanach + finalIncrement)
    firstBaseInside finalBaseInside firstDataInside finalDataInside initialStrain finalStrain frequency
  have dataDifference : (firstBase - standardCircleBanach + firstIncrement) -
      (finalBase - standardCircleBanach + finalIncrement) = (firstBase + firstIncrement) - (finalBase + finalIncrement) := by abel
  rw [dataDifference] at product
  have sumBound := by
    with_reducible_and_instances
      exact add_le_add (add_le_add (add_le_add (add_le_add shift lead) tail) primitive) product
  have collect : ∀ first second third fourth fifth : ℝ,
      0 ≤ first → 0 ≤ second → 0 ≤ third → 0 ≤ fourth → 0 ≤ fifth →
      shiftConstant * first + leadingConstant * second + seriesConstant * third +
        primitiveConstant * fourth + productConstant * fifth ≤
      constant * (first + second + third + fourth + fifth) := by
    intro first second third fourth fifth firstNonnegative secondNonnegative thirdNonnegative fourthNonnegative fifthNonnegative
    have firstLe : shiftConstant ≤ constant := by dsimp [constant]; linarith
    have secondLe : leadingConstant ≤ constant := by dsimp [constant]; linarith
    have thirdLe : seriesConstant ≤ constant := by dsimp [constant]; linarith
    have fourthLe : primitiveConstant ≤ constant := by dsimp [constant]; linarith
    have fifthLe : productConstant ≤ constant := by dsimp [constant]; linarith
    exact (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right firstLe firstNonnegative)
      (mul_le_mul_of_nonneg_right secondLe secondNonnegative))
      (mul_le_mul_of_nonneg_right thirdLe thirdNonnegative))
      (mul_le_mul_of_nonneg_right fourthLe fourthNonnegative))
      (mul_le_mul_of_nonneg_right fifthLe fifthNonnegative)).trans_eq (by ring)
  have scalar := collect
    (|frequency| * ((‖firstShift‖ + ‖finalShift‖) * ‖firstShift - finalShift‖ +
      ‖(firstBase + firstIncrement) - (finalBase + finalIncrement)‖ * ‖finalShift‖ ^ 2))
    (‖initialStrain‖ * ((‖firstIncrement‖ + ‖finalIncrement‖) * ‖firstIncrement - finalIncrement‖ +
      ‖firstBase - finalBase‖ * (‖firstIncrement‖ + ‖finalIncrement‖) ^ 2) +
      ‖initialStrain - finalStrain‖ * ‖finalIncrement‖ ^ 2)
    (((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖exteriorCoefficientWithoutLeading initialCoefficient degree‖) *
      (‖firstIncrement - finalIncrement‖ + ‖firstBase - finalBase‖ * ‖finalIncrement‖)) +
      (∑' degree, (96 : ℝ) ^ (degree + 1) *
        ‖exteriorCoefficientWithoutLeading initialCoefficient degree - exteriorCoefficientWithoutLeading finalCoefficient degree‖) *
        ‖finalIncrement‖)
    (|frequency| * (‖firstIncrement‖ * ‖firstPrimitive - finalPrimitive‖ +
      (‖firstIncrement - finalIncrement‖ + ‖firstBase - finalBase‖ * ‖finalIncrement‖) * ‖finalPrimitive‖))
    (|frequency|⁻¹ * (‖initialStrain‖ *
      (((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) +
        (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) *
        ‖(firstBase + firstIncrement) - (finalBase + finalIncrement)‖ +
        ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖) +
      (‖initialStrain‖ * ‖firstBase - finalBase‖ + ‖initialStrain - finalStrain‖) *
        (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  have algebra : canonicalExteriorStaticResidual phase frequency initialCoefficient firstBase firstIncrement firstShift firstPrimitive initialStrain -
      canonicalExteriorStaticResidual phase frequency finalCoefficient finalBase finalIncrement finalShift finalPrimitive finalStrain =
      (frequency • diskRotatingShiftError (firstBase + firstIncrement) firstShift -
        frequency • diskRotatingShiftError (finalBase + finalIncrement) finalShift) +
      (movingStrainAffineResidual firstBase initialStrain (firstBase + firstIncrement) -
        movingStrainAffineResidual finalBase finalStrain (finalBase + finalIncrement)) +
      ((circleBasedProjectedExteriorSeries phase (exteriorCoefficientWithoutLeading initialCoefficient)
        (firstBase - standardCircleBanach + firstIncrement) -
        circleBasedProjectedExteriorSeries phase (exteriorCoefficientWithoutLeading initialCoefficient) (firstBase - standardCircleBanach)) -
       (circleBasedProjectedExteriorSeries phase (exteriorCoefficientWithoutLeading finalCoefficient)
        (finalBase - standardCircleBanach + finalIncrement) -
        circleBasedProjectedExteriorSeries phase (exteriorCoefficientWithoutLeading finalCoefficient) (finalBase - standardCircleBanach))) +
      (frequency • ((fderiv ℝ diskEulerRotatingField (firstBase + firstIncrement) -
        fderiv ℝ diskEulerRotatingField firstBase) firstPrimitive) -
       frequency • ((fderiv ℝ diskEulerRotatingField (finalBase + finalIncrement) -
        fderiv ℝ diskEulerRotatingField finalBase) finalPrimitive)) -
      (frequency⁻¹ • (movingStrainRealCorrectionCLM firstBase initialStrain
        (circleBasedProjectedExteriorSeries phase initialCoefficient (firstBase - standardCircleBanach + firstIncrement))) -
       frequency⁻¹ • (movingStrainRealCorrectionCLM finalBase finalStrain
        (circleBasedProjectedExteriorSeries phase finalCoefficient (finalBase - standardCircleBanach + finalIncrement)))) := by
    unfold canonicalExteriorStaticResidual
    abel
  rw [algebra]
  with_reducible_and_instances
    apply (EulerNonuniqueness.General.norm_four_add_sub_le _ _ _ _ _).trans
    apply sumBound.trans
    convert scalar using 1 <;> dsimp only [canonicalExteriorStaticRelativeBudget] <;> simp only [div_eq_mul_inv] <;> ring

end EulerNonuniqueness.Paper
