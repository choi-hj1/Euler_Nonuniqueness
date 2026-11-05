import EulerNonuniqueness.Section5.CascadeIntegratedNonlinearCoefficient
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateLocalForeignHistory

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem integrated_coefficient_finite_coordinate_scalar_majorants
    {bound omega epsilon strain ratio macroRatio referenceSize size shape dilation moment center raw leading difference own macroForeign external
      gradedConstant momentConstant dilationConstant phaseConstant centerConstant : ℝ}
    (boundOne : 1 ≤ bound) (omegaOne : 1 ≤ omega)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (strainNonnegative : 0 ≤ strain) (strainOne : strain ≤ 1)
    (_ratioNonnegative : 0 ≤ ratio) (ratioOne : ratio ≤ 1)
    (_macroRatioNonnegative : 0 ≤ macroRatio) (macroRatioOne : macroRatio ≤ 1)
    (_referenceNonnegative : 0 ≤ referenceSize) (referenceOne : referenceSize ≤ 1)
    (shapeNonnegative : 0 ≤ shape) (shapeOne : shape ≤ 1) (shapeSize : shape ≤ size)
    (dilationNonnegative : 0 ≤ dilation) (dilationSize : dilation ≤ size)
    (_momentNonnegative : 0 ≤ moment) (momentSize : moment ≤ size)
    (centerNonnegative : 0 ≤ center) (centerSize : center ≤ bound * size)
    (rawNonnegative : 0 ≤ raw) (leadingNonnegative : 0 ≤ leading) (differenceNonnegative : 0 ≤ difference)
    (ownNonnegative : 0 ≤ own) (macroNonnegative : 0 ≤ macroForeign) (externalNonnegative : 0 ≤ external)
    (gradedNonnegative : 0 ≤ gradedConstant) (gradedBound : gradedConstant ≤ bound)
    (momentConstantNonnegative : 0 ≤ momentConstant) (momentBound : momentConstant ≤ bound)
    (dilationConstantNonnegative : 0 ≤ dilationConstant) (dilationBound : dilationConstant ≤ bound)
    (phaseConstantNonnegative : 0 ≤ phaseConstant) (phaseBound : phaseConstant ≤ bound)
    (centerConstantNonnegative : 0 ≤ centerConstant) (centerBound : centerConstant ≤ bound) :
    let budget := omega * (size + epsilon * raw) + (leading + difference + epsilon * macroForeign + epsilon * own + external)
    let graded := (referenceSize + dilation + shape) * shape + referenceSize * dilation
    gradedConstant * omega * graded + (moment + center + shape) +
        gradedConstant * omega * epsilon * (center + raw) + gradedConstant * epsilon * own +
        gradedConstant * macroRatio * (strain * center + difference) + gradedConstant * referenceSize * leading ≤
      20 * bound ^ 2 * budget ∧
    momentConstant * (strain * center + difference + epsilon * (strain * raw + macroForeign)) ≤ 4 * bound ^ 2 * budget ∧
    moment + (1 + dilationConstant * strain + dilationConstant * omega * epsilon) * center +
        dilationConstant * omega * epsilon * raw + dilationConstant * difference + dilationConstant * epsilon * own ≤
      7 * bound ^ 2 * budget ∧
    2 * omega * dilation + omega * shape + (moment + center + shape) +
        phaseConstant * omega * epsilon * (center + raw) + phaseConstant * difference + phaseConstant * epsilon * own ≤
      10 * bound ^ 2 * budget ∧
    moment + center + external + centerConstant * omega * ratio * epsilon * (center + raw) +
        centerConstant * ratio * epsilon * own ≤ 6 * bound ^ 2 * budget := by
  dsimp only
  let budget := omega * (size + epsilon * raw) + (leading + difference + epsilon * macroForeign + epsilon * own + external)
  change _ ≤ 20 * bound ^ 2 * budget ∧ _ ≤ 4 * bound ^ 2 * budget ∧ _ ≤ 7 * bound ^ 2 * budget ∧
    _ ≤ 10 * bound ^ 2 * budget ∧ _ ≤ 6 * bound ^ 2 * budget
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have sizeNonnegative : 0 ≤ size := shapeNonnegative.trans shapeSize
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have omegaPartNonnegative := mul_nonneg omegaNonnegative sizeNonnegative
  have rawPartNonnegative := mul_nonneg omegaNonnegative (mul_nonneg epsilonNonnegative rawNonnegative)
  have macroPartNonnegative := mul_nonneg epsilonNonnegative macroNonnegative
  have ownPartNonnegative := mul_nonneg epsilonNonnegative ownNonnegative
  have omegaSize : omega * size ≤ budget := by
    dsimp only [budget]
    nlinarith only [rawPartNonnegative, leadingNonnegative, differenceNonnegative,
      macroPartNonnegative, ownPartNonnegative, externalNonnegative]
  have rawBudget : omega * epsilon * raw ≤ budget := by
    dsimp only [budget]
    nlinarith only [omegaPartNonnegative, leadingNonnegative, differenceNonnegative,
      macroPartNonnegative, ownPartNonnegative, externalNonnegative]
  have leadingBudget : leading ≤ budget := by
    dsimp only [budget]
    nlinarith only [omegaPartNonnegative, rawPartNonnegative, differenceNonnegative, macroPartNonnegative, ownPartNonnegative, externalNonnegative]
  have differenceBudget : difference ≤ budget := by
    dsimp only [budget]
    nlinarith only [omegaPartNonnegative, rawPartNonnegative, leadingNonnegative, macroPartNonnegative, ownPartNonnegative, externalNonnegative]
  have ownBudget : epsilon * own ≤ budget := by
    dsimp only [budget]
    nlinarith only [omegaPartNonnegative, rawPartNonnegative, leadingNonnegative, differenceNonnegative, macroPartNonnegative, externalNonnegative]
  have macroBudget : epsilon * macroForeign ≤ budget := by
    dsimp only [budget]
    nlinarith only [omegaPartNonnegative, rawPartNonnegative, leadingNonnegative, differenceNonnegative, ownPartNonnegative, externalNonnegative]
  have externalBudget : external ≤ budget := by
    dsimp only [budget]
    nlinarith only [omegaPartNonnegative, rawPartNonnegative, leadingNonnegative, differenceNonnegative, macroPartNonnegative, ownPartNonnegative]
  have sizeBudget : size ≤ budget := (le_mul_of_one_le_left sizeNonnegative omegaOne).trans omegaSize
  have momentBudget := momentSize.trans sizeBudget
  have shapeBudget := shapeSize.trans sizeBudget
  have centerBudget := centerSize.trans (mul_le_mul_of_nonneg_left sizeBudget boundNonnegative)
  have strainCenter : strain * center ≤ bound * budget :=
    (mul_le_of_le_one_left centerNonnegative strainOne).trans centerBudget
  have epsilonCenter : omega * epsilon * center ≤ bound * budget := by
    calc
      _ ≤ omega * center := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_left centerNonnegative epsilonOne) omegaNonnegative
      _ ≤ omega * (bound * size) := mul_le_mul_of_nonneg_left centerSize omegaNonnegative
      _ ≤ bound * budget := by simpa only [mul_left_comm omega bound] using mul_le_mul_of_nonneg_left omegaSize boundNonnegative
  have selfBudget : omega * epsilon * (center + raw) ≤ (bound + 1) * budget := by nlinarith only [epsilonCenter, rawBudget]
  have strainRaw : epsilon * strain * raw ≤ budget := by
    calc
      _ ≤ epsilon * raw := by nlinarith only [mul_le_mul_of_nonneg_right strainOne (mul_nonneg epsilonNonnegative rawNonnegative)]
      _ ≤ omega * epsilon * raw := by nlinarith only [mul_le_mul_of_nonneg_right omegaOne (mul_nonneg epsilonNonnegative rawNonnegative)]
      _ ≤ budget := rawBudget
  have gradedSize : (referenceSize + dilation + shape) * shape + referenceSize * dilation ≤ 4 * size := by
    have first := mul_le_of_le_one_left shapeNonnegative referenceOne
    have second := mul_le_of_le_one_right dilationNonnegative shapeOne
    have third := mul_le_of_le_one_right shapeNonnegative shapeOne
    have fourth := mul_le_of_le_one_left dilationNonnegative referenceOne
    nlinarith only [first, second, third, fourth, shapeSize, dilationSize]
  have gradedBudget : omega * ((referenceSize + dilation + shape) * shape + referenceSize * dilation) ≤ 4 * budget := by
    have actual := mul_le_mul_of_nonneg_left gradedSize omegaNonnegative
    nlinarith only [actual, omegaSize]
  have macroRatioBudget : macroRatio * (strain * center + difference) ≤ (bound + 1) * budget := by
    have actual := mul_le_of_le_one_left (add_nonneg (mul_nonneg strainNonnegative centerNonnegative) differenceNonnegative) macroRatioOne
    nlinarith only [actual, strainCenter, differenceBudget]
  have referenceBudget : referenceSize * leading ≤ budget :=
    (mul_le_of_le_one_left leadingNonnegative referenceOne).trans leadingBudget
  have ratioSelf : ratio * (omega * epsilon * (center + raw)) ≤ (bound + 1) * budget :=
    (mul_le_of_le_one_left (mul_nonneg (mul_nonneg omegaNonnegative epsilonNonnegative)
      (add_nonneg centerNonnegative rawNonnegative)) ratioOne).trans selfBudget
  have ratioOwn : ratio * (epsilon * own) ≤ budget :=
    (mul_le_of_le_one_left (mul_nonneg epsilonNonnegative ownNonnegative) ratioOne).trans ownBudget
  have multiply {constant value coefficient : ℝ} (constantNonnegative : 0 ≤ constant) (constantBound : constant ≤ bound)
      (valueBound : value ≤ coefficient * budget) (coefficientNonnegative : 0 ≤ coefficient) :
      constant * value ≤ bound * coefficient * budget :=
    (mul_le_mul_of_nonneg_left valueBound constantNonnegative).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right constantBound (mul_nonneg coefficientNonnegative budgetNonnegative))
  have coefficientBounds : 2 * bound ^ 2 + 9 * bound + 2 ≤ 20 * bound ^ 2 ∧
      bound ^ 2 + 3 * bound ≤ 4 * bound ^ 2 ∧ 2 * bound ^ 2 + 4 * bound + 1 ≤ 7 * bound ^ 2 ∧
      bound ^ 2 + 4 * bound + 5 ≤ 10 * bound ^ 2 ∧ bound ^ 2 + 3 * bound + 2 ≤ 6 * bound ^ 2 := by
    constructor <;> (try constructor) <;> (try constructor) <;> (try constructor) <;> nlinarith only [boundOne, sq_nonneg (bound - 1)]
  have gradedFinal := multiply gradedNonnegative gradedBound gradedBudget (by norm_num)
  have gradedSelf := multiply gradedNonnegative gradedBound selfBudget (by linarith only [boundOne])
  have gradedOwn := multiply (coefficient := 1) gradedNonnegative gradedBound (by simpa only [one_mul] using ownBudget) (by norm_num)
  have gradedMacro := multiply gradedNonnegative gradedBound macroRatioBudget (by linarith only [boundOne])
  have gradedLeading := multiply (coefficient := 1) gradedNonnegative gradedBound (by simpa only [one_mul] using referenceBudget) (by norm_num)
  have momentForcing : strain * center + difference + epsilon * (strain * raw + macroForeign) ≤ (bound + 3) * budget := by
    nlinarith only [strainCenter, differenceBudget, strainRaw, macroBudget]
  have momentFinal := multiply momentConstantNonnegative momentBound momentForcing (by linarith only [boundOne])
  have dilationStrain := multiply dilationConstantNonnegative dilationBound strainCenter boundNonnegative
  have dilationCenter := multiply dilationConstantNonnegative dilationBound epsilonCenter boundNonnegative
  have dilationRaw := multiply (coefficient := 1) dilationConstantNonnegative dilationBound (by simpa only [one_mul] using rawBudget) (by norm_num)
  have dilationDifference := multiply (coefficient := 1) dilationConstantNonnegative dilationBound (by simpa only [one_mul] using differenceBudget) (by norm_num)
  have dilationOwn := multiply (coefficient := 1) dilationConstantNonnegative dilationBound (by simpa only [one_mul] using ownBudget) (by norm_num)
  have phaseSelf := multiply phaseConstantNonnegative phaseBound selfBudget (by linarith only [boundOne])
  have phaseDifference := multiply (coefficient := 1) phaseConstantNonnegative phaseBound (by simpa only [one_mul] using differenceBudget) (by norm_num)
  have phaseOwn := multiply (coefficient := 1) phaseConstantNonnegative phaseBound (by simpa only [one_mul] using ownBudget) (by norm_num)
  have omegaDilation := (mul_le_mul_of_nonneg_left dilationSize omegaNonnegative).trans omegaSize
  have omegaShape := (mul_le_mul_of_nonneg_left shapeSize omegaNonnegative).trans omegaSize
  have centerSelf := multiply centerConstantNonnegative centerBound ratioSelf (by linarith only [boundOne])
  have centerOwn := multiply (coefficient := 1) centerConstantNonnegative centerBound (by simpa only [one_mul] using ratioOwn) (by norm_num)
  have coefficients := And.intro (mul_le_mul_of_nonneg_right coefficientBounds.1 budgetNonnegative)
    (And.intro (mul_le_mul_of_nonneg_right coefficientBounds.2.1 budgetNonnegative)
      (And.intro (mul_le_mul_of_nonneg_right coefficientBounds.2.2.1 budgetNonnegative)
        (And.intro (mul_le_mul_of_nonneg_right coefficientBounds.2.2.2.1 budgetNonnegative)
          (mul_le_mul_of_nonneg_right coefficientBounds.2.2.2.2 budgetNonnegative))))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [gradedFinal, gradedSelf, gradedOwn, gradedMacro, gradedLeading, momentBudget, centerBudget, shapeBudget, coefficients.1]
  · nlinarith only [momentFinal, coefficients.2.1]
  · nlinarith only [momentBudget, centerBudget, dilationStrain, dilationCenter, dilationRaw, dilationDifference, dilationOwn, coefficients.2.2.1]
  · nlinarith only [omegaDilation, omegaShape, momentBudget, centerBudget, shapeBudget, phaseSelf, phaseDifference, phaseOwn, coefficients.2.2.2.1]
  · nlinarith only [momentBudget, centerBudget, externalBudget, centerSelf, centerOwn, coefficients.2.2.2.2]

theorem exists_uniform_actual_integrated_coefficient_finite_coordinate_history :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ actionDilationConstant ≥ (0 : ℝ), ∃ finiteConstant ≥ (1 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant → 0 < tolerance →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let relative := fun time => referenceStraightenedShape first graph coordinate index time -
        referenceStraightenedShape second graph coordinate index time
      let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time index
      let remainder := relativeStraightenedSaddleStrainRemainder changed
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index
      let omega := changed.omega (index.val + 1)
      let growth := 2 * Real.sqrt 2 * omega
      let length := changed.length (index.val + 1)
      let centerRadius := factor / 39321600 * changed.location (index.val + 1)
      let patchRadius := factor / 39321600 * length
      let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
      let center := fun time => prepared.rawSourceCenteredState time index
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let moment := fun time => ‖relativeNormalizedFirstMoment changed first second index time‖
      let shape := fun time => |(relative time).1| + |(relative time).2|
      let dilation := fun time => |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
      let indexedReferenceSize := chartConstant * referenceConstant *
        ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
      let coefficient := fun time => indexedReferenceSize + dilation time + |(relative time).2|
      let graded := fun time => coefficient time * shape time + indexedReferenceSize * dilation time
      let difference := fun time => ∑' power : ℕ,
        ‖quadrupoleExteriorCoefficient changed first index time centerRadius power -
          quadrupoleExteriorCoefficient changed second index time centerRadius power‖
      let firstFamily := prepared.trajectory.movingFamily
      let secondFamily := prepared.referenceWitness.trajectory.movingFamily
      let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid firstFamily.patchMotion current index patch) patchRadius (power + 1) time -
          secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid secondFamily.patchMotion current index patch) patchRadius (power + 1) time‖
      let dilationMajorant := fun time => tolerance * moment time +
        (tolerance + actionDilationConstant * changed.strain + actionDilationConstant * omega * epsilon) * center time +
        actionDilationConstant * omega * epsilon * raw time + actionDilationConstant * difference time +
        actionDilationConstant * epsilon * ∑ patch : Fin 4, foreign patch time
      let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖
      let upper := fun time => stableConstant * omega * graded time + tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖
      (ContinuousOn coefficient (Icc 0 finish) ∧ ContinuousOn dilationMajorant (Icc 0 finish) ∧
      ContinuousOn forcing (Icc 0 finish) ∧
      IntervalIntegrable coefficient volume 0 finish ∧
      IntervalIntegrable (fun time => (finish - time) * dilationMajorant time) volume 0 finish ∧
      IntervalIntegrable forcing volume 0 finish ∧
      (omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤
        2 * omega * indexedReferenceSize * finish +
          2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
          ∫ time in (0 : ℝ)..finish, forcing time) ∧
      0 < growth ∧ ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn leading (Icc 0 finish) ∧
      ContinuousOn remainder (Icc 0 finish) ∧
      IntervalIntegrable (fun time => ‖remainder time‖) volume 0 finish ∧
      IntervalIntegrable upper volume 0 finish ∧
      (∀ time ∈ Ioo 0 finish, ‖remainder time‖ ≤ upper time) ∧
      (∀ time ∈ Icc 0 finish,
        (∫ current in (0 : ℝ)..time, ‖remainder current‖) ≤ ∫ current in (0 : ℝ)..time, upper current ∧
        Real.exp (-growth * time) * (relative time).1 =
          (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1) +
            ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1 ∧
        (relative time).2 = ∫ current in (0 : ℝ)..time,
          Real.exp (-growth * (time - current)) * (leading current + remainder current).2 ∧
        |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
          Real.exp (-growth * (time - current)) * (|(leading current).2| + upper current)) ∧
      growth * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(relative time).2|) ≤
        (1 / 2 : ℝ) * ((∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(leading time).2|) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * upper time)) ∧
      ∃ lift : Fin 2 → ℝ → ℝ,
        (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
        (∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
              Complex.exp (Complex.I * (lift side time : ℂ))) ∧
        ContinuousOn (prepared.finiteCoordinateSize graph coordinate lift index) (Icc 0 finish) ∧
        prepared.finiteCoordinateSize graph coordinate lift index 0 = 0 ∧
        ContinuousOn (prepared.finiteCoordinateForeignForcing index) (Icc 0 finish) ∧
        IntervalIntegrable (prepared.finiteCoordinateForeignForcing index) volume 0 finish ∧
        ∀ time ∈ Icc 0 finish,
          prepared.finiteCoordinateSize graph coordinate lift index time ≤ finiteConstant *
            ∫ current in (0 : ℝ)..time,
              ({scales with frequency := frequency} : Scales).omega (index.val + 1) *
                (prepared.finiteCoordinateSize graph coordinate lift index current +
                  (({scales with frequency := frequency} : Scales).radius (index.val + 1) ^ 2 /
                    ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2) *
                    ∑ patch : Fin 4, prepared.rawSourceShapeBudget current index patch) +
                prepared.finiteCoordinateForeignForcing index current := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, gradedThreshold, gradedThresholdPositive, gradedThresholdEighth, compatible,
    gradedCap, gradedCapPositive, gradedFactory⟩ :=
    exists_uniform_actual_integrated_nonlinear_coefficient
  obtain ⟨geometryRadius, geometryPositive, geometryQuarter, geometryConstant, geometryOne, geometryFactory⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨phaseThreshold, phaseThresholdPositive, _, phaseCap, phaseCapPositive, phaseFactory⟩ :=
    exists_uniform_actual_cascade_corrected_phase_local_foreign_history graphAnalytic graphZero graphDerivative coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨momentCap, momentCapPositive, momentFactory⟩ := exists_uniform_actual_firstMoment_local_foreign_history
  obtain ⟨dilationCap, dilationCapPositive, dilationFactory⟩ := exists_uniform_actual_prehit_dilation_local_foreign_history
  obtain ⟨centerCap, centerCapPositive, centerFactory⟩ := exists_uniform_actual_center_local_foreign_history
  obtain ⟨stateCap, stateCapPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨equationRadius, equationPositive, _, equations⟩ :=
    exists_uniform_cascade_closed_saddle_dynamics (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
  have chartRegular := localNormalFormChart_regular (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  have chartNear := chartRegular.1.continuousAt.norm.eventually
    (eventually_lt_nhds (show ‖localNormalFormChart graph coordinate (0 : ℝ × ℝ)‖ < (1 / 4 : ℝ) by rw [chartRegular.2.1, norm_zero]; norm_num))
  obtain ⟨chartRadius, chartPositive, chartInside⟩ := Metric.mem_nhds_iff.mp chartNear
  let rawCap := min gradedCap (min momentCap (min dilationCap (min phaseCap (min centerCap stateCap))))
  have capPositive : 0 < rawCap := lt_min gradedCapPositive (lt_min momentCapPositive (lt_min dilationCapPositive
    (lt_min phaseCapPositive (lt_min centerCapPositive stateCapPositive))))
  have capGraded : rawCap ≤ gradedCap := min_le_left _ _
  have capMoment : rawCap ≤ momentCap := (min_le_right _ _).trans (min_le_left _ _)
  have capDilation : rawCap ≤ dilationCap := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have capPhase : rawCap ≤ phaseCap := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have capCenter : rawCap ≤ centerCap := ((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have capState : rawCap ≤ stateCap := ((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  let thresholdMax := min gradedThreshold phaseThreshold
  have thresholdPositive : 0 < thresholdMax := lt_min gradedThresholdPositive phaseThresholdPositive
  have thresholdEighth : thresholdMax ≤ 1 / 8 := (min_le_left _ _).trans gradedThresholdEighth
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth, compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨gradedConstant, gradedOne, actionDilationConstant, actionDilationNonnegative,
    gradedRadius, gradedPositive, gradedQuarter, gradedParameters⟩ := gradedFactory factorPositive factorSmall
  obtain ⟨momentConstant, momentNonnegative, momentParameters⟩ := momentFactory factorPositive factorEighth
  obtain ⟨historyDilationConstant, dilationNonnegative, dilationParameters⟩ := dilationFactory factorPositive factorSmall
  obtain ⟨phaseConstant, phaseNonnegative, phaseParameters⟩ := phaseFactory factorPositive factorEighth
  obtain ⟨phaseRadius, phasePositive, _, phaseParameters⟩ := phaseParameters 1 (by norm_num)
  obtain ⟨centerConstant, centerNonnegative, centerParameters⟩ := centerFactory factorPositive factorSmall
  let bound := 1 + geometryConstant + gradedConstant + momentConstant + historyDilationConstant + phaseConstant + centerConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith only [geometryOne, gradedOne, momentNonnegative, dilationNonnegative, phaseNonnegative, centerNonnegative]
  have boundGeometry : geometryConstant ≤ bound := by dsimp only [bound]; linarith only [gradedOne, momentNonnegative, dilationNonnegative, phaseNonnegative, centerNonnegative]
  have boundGraded : gradedConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, momentNonnegative, dilationNonnegative, phaseNonnegative, centerNonnegative]
  have boundMoment : momentConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, gradedOne, dilationNonnegative, phaseNonnegative, centerNonnegative]
  have boundDilation : historyDilationConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, gradedOne, momentNonnegative, phaseNonnegative, centerNonnegative]
  have boundPhase : phaseConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, gradedOne, momentNonnegative, dilationNonnegative, centerNonnegative]
  have boundCenter : centerConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, gradedOne, momentNonnegative, dilationNonnegative, phaseNonnegative]
  let referenceRadius := min equationRadius chartRadius
  let radius := min geometryRadius (min gradedRadius (min phaseRadius (referenceRadius / 2)))
  have referencePositive : 0 < referenceRadius := lt_min equationPositive chartPositive
  have radiusPositive : 0 < radius := lt_min geometryPositive (lt_min gradedPositive (lt_min phasePositive (by positivity)))
  have radiusGeometry : radius ≤ geometryRadius := min_le_left _ _
  have radiusGraded : radius ≤ gradedRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusPhase : radius ≤ phaseRadius := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have radiusReference : radius < referenceRadius := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans_lt (by linarith only [referencePositive])
  have radiusQuarter : radius ≤ 1 / 4 := radiusGeometry.trans geometryQuarter
  refine ⟨gradedConstant, gradedOne, actionDilationConstant, actionDilationNonnegative,
    100 * bound ^ 2, by nlinarith only [boundOne, sq_nonneg (bound - 1)], radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant tolerance rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [gradedParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    gradedParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative tolerancePositive,
    geometryFactory scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne)
      factorPositive factorEighth thresholdSmall referenceNonnegative,
    momentParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    dilationParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    phaseParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne (thresholdBound.trans (min_le_right _ _)) referenceNonnegative,
    centerParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_patch_external_velocity_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative referencePositive,
    scales.eventually_uniform_reference_index_budget_small ratioBound alphaPositive
      (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (show (0 : ℝ) < factor / 39321600 by positivity),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)]
    with frequency gradedEstimate retainedEstimate geometryEstimate momentEstimate dilationEstimate phaseEstimate centerEstimate seriesContinuous coherence externalContinuous referenceSmall referenceBudget lengths radii strainSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  have centeredCapInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceCenteredState = prepared.rawSourceCenteredState := by rfl
  have rawCapInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by rfl
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let macroRadius := factor / 39321600 * changed.location (index.val + 1)
  let ownRadius := factor / 39321600 * changed.length (index.val + 1)
  let relative := fun time => referenceStraightenedShape first graph coordinate index time - referenceStraightenedShape second graph coordinate index time
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let dilation := fun time => |diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first second index time‖
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time index
  let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time macroRadius power - quadrupoleExteriorCoefficient changed second index time macroRadius power‖
  let foreign := fun receiverRadius (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first current index patch) receiverRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch) receiverRadius (power + 1) time‖
  let external := fun time => (∑ patch : Fin 4, ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
    biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) / (4 * changed.location (index.val + 1))
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonOne : epsilon ≤ 1 := by
    have radiusBound := (radii (index.val + 1)).le
    change changed.radius (index.val + 1) ≤ 1 * changed.length (index.val + 1) at radiusBound
    exact (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
      (pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le (by simpa only [one_mul] using radiusBound) 2)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have referenceNonnegative' : 0 ≤ referenceSize := by simpa only [referenceSize, omega, mul_assoc] using (referenceBudget (index.val + 1)).1
  have referenceOne : referenceSize ≤ 1 := by simpa only [referenceSize, omega, mul_assoc] using (referenceBudget (index.val + 1)).2.le
  have ratioOne : changed.length (index.val + 1) / changed.location (index.val + 1) ≤ 1 := by
    apply (div_le_one (changed.location_pos _)).mpr
    have actual := (lengths (index.val + 1)).le
    have coefficient : factor / 39321600 ≤ (1 : ℝ) := by linarith only [factorSmall]
    exact actual.trans (mul_le_of_le_one_left (changed.location_pos _).le coefficient)
  have macroRatioOne : changed.length (index.val + 1) / macroRadius ≤ 1 :=
    (div_le_one (mul_pos (by positivity) (changed.location_pos _))).mpr (lengths (index.val + 1)).le
  obtain ⟨lift, liftContinuous, polar, coordinateContinuous, coordinateInitial, coordinateNonnegative, geometryBounds⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound (fun time inside => (small time inside).trans radiusGeometry)
  let size := prepared.finiteCoordinateSize graph coordinate lift index
  let phaseValue := fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|
  let translation := fun time => ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1)
  let forcing := prepared.finiteCoordinateForeignForcing index
  let budget := fun time => omega * (size time + epsilon * raw time) + forcing time
  have sizeIdentity (time : ℝ) : size time = shape time + dilation time + phaseValue time + moment time + translation time := by
    dsimp only [size, shape, relative, dilation, phaseValue, moment, translation, CascadeSourcePreparedPair.finiteCoordinateSize, first, second, changed, Prod.fst_sub, Prod.snd_sub]
  have forcingIdentity (time : ℝ) : forcing time = ‖leading time‖ + difference time + epsilon * (∑ patch : Fin 4, foreign macroRadius patch time) +
      epsilon * (∑ patch : Fin 4, foreign ownRadius patch time) + external time := by
    dsimp only [forcing, CascadeSourcePreparedPair.finiteCoordinateForeignForcing, leading, difference, foreign, macroRadius, ownRadius, epsilon, external, first, second, changed]
    rw [prepared.referenceIdentity]
  have allNonnegative (time : ℝ) : 0 ≤ shape time ∧ 0 ≤ dilation time ∧ 0 ≤ phaseValue time ∧ 0 ≤ moment time ∧ 0 ≤ translation time ∧
      0 ≤ center time ∧ 0 ≤ raw time ∧ 0 ≤ difference time ∧ (∀ receiverRadius, 0 ≤ ∑ patch : Fin 4, foreign receiverRadius patch time) ∧ 0 ≤ external time := by
    refine ⟨add_nonneg (abs_nonneg _) (abs_nonneg _), div_nonneg (abs_nonneg _) (sq_nonneg _), abs_nonneg _, norm_nonneg _,
      div_nonneg (norm_nonneg _) (changed.location_pos _).le, div_nonneg (norm_nonneg _) (changed.length_pos _).le,
      ?_, tsum_nonneg (fun _ => norm_nonneg _), ?_, div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        (mul_nonneg (by norm_num) (changed.location_pos _).le)⟩
    · apply Finset.sum_nonneg
      intro patch _
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    · intro receiverRadius
      exact Finset.sum_nonneg (fun _ _ => tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _)))
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < referenceRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusReference
    · have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
      change |unstableShape second time index| + |stableShape second time index| < referenceRadius
      linarith only [actual, abs_nonneg (diagonalDifference second time index / changed.length (index.val + 1) ^ 2 - 1)]
  have shapeOne (time : ℝ) (inside : time ∈ Icc 0 finish) : shape time ≤ 1 := by
    have chartSmall (side : Fin 2) : ‖referenceStraightenedShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) graph coordinate index time‖ < (1 / 4 : ℝ) := by
      apply chartInside
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))).trans_lt
        ((pairedSmall side time inside).trans_le (min_le_right _ _))
    have firstSmall := chartSmall 0
    have secondSmall := chartSmall 1
    change ‖referenceStraightenedShape first graph coordinate index time‖ < (1 / 4 : ℝ) at firstSmall
    change ‖referenceStraightenedShape second graph coordinate index time‖ < (1 / 4 : ℝ) at secondSmall
    have firstFst := norm_fst_le (referenceStraightenedShape first graph coordinate index time)
    have firstSnd := norm_snd_le (referenceStraightenedShape first graph coordinate index time)
    have secondFst := norm_fst_le (referenceStraightenedShape second graph coordinate index time)
    have secondSnd := norm_snd_le (referenceStraightenedShape second graph coordinate index time)
    simp only [Real.norm_eq_abs] at firstFst firstSnd secondFst secondSnd
    dsimp only [shape, relative, Prod.fst_sub, Prod.snd_sub]
    nlinarith only [abs_sub (referenceStraightenedShape first graph coordinate index time).1 (referenceStraightenedShape second graph coordinate index time).1,
      abs_sub (referenceStraightenedShape first graph coordinate index time).2 (referenceStraightenedShape second graph coordinate index time).2,
      firstFst, firstSnd, secondFst, secondSnd, firstSmall, secondSmall]
  have graded := gradedEstimate count phase dipoleAngle (prepared.enlargeCap capGraded) path index nonterminal finish finishNonnegative finishBound radialSmall
    (fun time inside => (small time inside).trans radiusGraded)
  have retained := retainedEstimate count phase dipoleAngle (prepared.enlargeCap capGraded) path index nonterminal finish finishNonnegative finishBound radialSmall
    (fun time inside => (small time inside).trans radiusGraded)
  obtain ⟨_, _, _, _, _, _, _, growthPositive, relativeContinuous, leadingContinuous, _, _, _, remainderBound, _, _⟩ := graded
  have momentHistory := momentEstimate count phase dipoleAngle (prepared.enlargeCap capMoment) path index nonterminal finish finishNonnegative finishBound radialSmall
  have dilationHistory := dilationEstimate count phase dipoleAngle (prepared.enlargeCap capDilation) path index nonterminal finish finishNonnegative finishBound radialSmall
  have centerHistory := centerEstimate count phase dipoleAngle (prepared.enlargeCap capCenter) path index nonterminal finish finishNonnegative finishBound radialSmall
  have phaseHistory := phaseEstimate count phase dipoleAngle (prepared.enlargeCap capPhase) path index nonterminal finish finishNonnegative finishBound radialSmall
    (fun time inside => (small time inside).trans radiusPhase)
  simp only [centeredCapInvariant, rawCapInvariant] at momentHistory dilationHistory centerHistory phaseHistory remainderBound retained
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at momentHistory dilationHistory centerHistory phaseHistory relativeContinuous leadingContinuous remainderBound retained
  rw [← prepared.referenceIdentity] at momentHistory dilationHistory centerHistory
  obtain ⟨phaseLift, phaseLiftContinuous, _, phasePolar, _, _, _, _, _, _, _, phaseUpperIntegrable, _, phasePrimitive⟩ := phaseHistory
  have phaseEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans radiusQuarter) lift phaseLift
    (fun side => (liftContinuous side).1.continuousOn) (fun side => (phaseLiftContinuous side).1.continuousOn)
    (fun side => (liftContinuous side).2.trans (phaseLiftContinuous side).2.symm) polar phasePolar).2.1 (phaseCorrection 1 graph)
  have radiusSmall (receiverRadius : ℝ) (nonnegative : 0 ≤ receiverRadius) (upper : receiverRadius ≤ macroRadius) :
      receiverRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have locationPositive := changed.location_pos (index.val + 1)
    change receiverRadius ≤ changed.location (index.val + 1) / (100000 * 96)
    dsimp only [macroRadius] at upper
    nlinarith only [upper, locationPositive, mul_nonneg (sub_nonneg.mpr factorSmall) locationPositive.le]
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.location_pos _).le
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.length_pos _).le
  have ownMacro : ownRadius ≤ macroRadius := mul_le_mul_of_nonneg_left
    ((div_le_one (changed.location_pos _)).mp ratioOne) (div_nonneg factorPositive.le (by norm_num))
  have seriesMacro := seriesContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index macroRadius macroNonnegative
    (radiusSmall macroRadius macroNonnegative le_rfl)
  have seriesOwn := seriesContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index ownRadius ownNonnegative
    (radiusSmall ownRadius ownNonnegative ownMacro)
  have differenceContinuous : ContinuousOn difference (Icc 0 finish) := by
    have actual := seriesMacro.2.2.mono subset
    rw [← prepared.referenceIdentity] at actual
    exact actual
  have foreignContinuous (receiverRadius : ℝ) (which : receiverRadius = macroRadius ∨ receiverRadius = ownRadius) :
      ContinuousOn (fun time => ∑ patch : Fin 4, foreign receiverRadius patch time) (Icc 0 finish) := by
    rcases which with rfl | rfl
    · exact continuousOn_finset_sum _ (fun patch _ => ((seriesMacro.1 patch).2.mono subset))
    · exact continuousOn_finset_sum _ (fun patch _ => ((seriesOwn.1 patch).2.mono subset))
  have externalC0 : ContinuousOn external (Icc 0 finish) := by
    have actual := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
      (externalContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).norm.mono subset)
    rw [← prepared.referenceIdentity] at actual
    exact actual.div_const _
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := by
    apply ((((leadingContinuous.norm.add differenceContinuous).add
      (continuousOn_const.mul (foreignContinuous macroRadius (Or.inl rfl)))).add
      (continuousOn_const.mul (foreignContinuous ownRadius (Or.inr rfl)))).add externalC0).congr
    intro time _
    exact forcingIdentity time
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _
    (fun patch _ => ((stateContinuity prepared capPositive capState path index).1 patch).mono subset)
  have centerContinuous : ContinuousOn center (Icc 0 finish) := (stateContinuity prepared capPositive capState path index).2.1.mono subset
  have budgetContinuous : ContinuousOn budget (Icc 0 finish) :=
    (continuousOn_const.mul (coordinateContinuous.add (continuousOn_const.mul rawContinuous))).add forcingContinuous
  have budgetNonnegative (time : ℝ) : 0 ≤ budget time := by
    rw [show budget time = omega * (size time + epsilon * raw time) + forcing time from rfl, forcingIdentity]
    obtain ⟨_, _, _, _, _, _, rawNonnegative, differenceNonnegative, foreignNonnegative, externalNonnegative⟩ := allNonnegative time
    have ownNonnegative' := foreignNonnegative ownRadius
    have macroNonnegative' := foreignNonnegative macroRadius
    have sizeNonnegative : 0 ≤ size time := coordinateNonnegative time
    exact add_nonneg (mul_nonneg omegaNonnegative (add_nonneg sizeNonnegative (mul_nonneg epsilonNonnegative rawNonnegative)))
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) differenceNonnegative)
        (mul_nonneg epsilonNonnegative macroNonnegative')) (mul_nonneg epsilonNonnegative ownNonnegative')) externalNonnegative)
  have budgetComponents (time : ℝ) : omega * size time ≤ budget time ∧ ‖leading time‖ ≤ budget time := by
    obtain ⟨_, _, _, _, _, _, rawNonnegative, differenceNonnegative, foreignNonnegative, externalNonnegative⟩ := allNonnegative time
    have ownPart := mul_nonneg epsilonNonnegative (foreignNonnegative ownRadius)
    have macroPart := mul_nonneg epsilonNonnegative (foreignNonnegative macroRadius)
    have rawPart := mul_nonneg omegaNonnegative (mul_nonneg epsilonNonnegative rawNonnegative)
    have sizeNonnegative : 0 ≤ size time := coordinateNonnegative time
    have sizePart := mul_nonneg omegaNonnegative sizeNonnegative
    dsimp only [budget]
    rw [forcingIdentity]
    constructor <;> nlinarith only [ownPart, macroPart, rawPart, sizePart, differenceNonnegative, externalNonnegative, norm_nonneg (leading time)]
  let momentUpper := fun time => momentConstant * (changed.strain * center time + difference time + epsilon *
    (changed.strain * raw time + ∑ patch : Fin 4, foreign macroRadius patch time))
  let dilationUpper := fun time => moment time + (1 + historyDilationConstant * changed.strain + historyDilationConstant * omega * epsilon) * center time +
    historyDilationConstant * omega * epsilon * raw time + historyDilationConstant * difference time + historyDilationConstant * epsilon * ∑ patch : Fin 4, foreign ownRadius patch time
  let phaseUpper := fun time => 2 * omega * dilation time + omega * shape time + (moment time + center time + shape time) +
    phaseConstant * omega * epsilon * (center time + raw time) + phaseConstant * difference time + phaseConstant * epsilon * ∑ patch : Fin 4, foreign ownRadius patch time
  let centerUpper := fun time => moment time + center time + external time + centerConstant * omega *
    (changed.length (index.val + 1) / changed.location (index.val + 1)) * epsilon * (center time + raw time) +
    centerConstant * (changed.length (index.val + 1) / changed.location (index.val + 1)) * epsilon * ∑ patch : Fin 4, foreign ownRadius patch time
  let remainderUpper := fun time => gradedConstant * omega * ((referenceSize + dilation time + shape time) * shape time + referenceSize * dilation time) +
    (moment time + center time + shape time) + gradedConstant * omega * epsilon * (center time + raw time) +
    gradedConstant * epsilon * (∑ patch : Fin 4, foreign ownRadius patch time) +
    gradedConstant * (changed.length (index.val + 1) / macroRadius) * (changed.strain * center time + difference time) + gradedConstant * referenceSize * ‖leading time‖
  have scalarBounds (time : ℝ) (inside : time ∈ Icc 0 finish) :
      remainderUpper time ≤ 20 * bound ^ 2 * budget time ∧ momentUpper time ≤ 4 * bound ^ 2 * budget time ∧
      dilationUpper time ≤ 7 * bound ^ 2 * budget time ∧ phaseUpper time ≤ 10 * bound ^ 2 * budget time ∧ centerUpper time ≤ 6 * bound ^ 2 * budget time := by
    obtain ⟨shapeNonnegative, dilationNonnegative', phaseValueNonnegative, momentNonnegative', translationNonnegative,
      centerNonnegative', rawNonnegative, differenceNonnegative, foreignNonnegative, externalNonnegative⟩ := allNonnegative time
    have shapeSize : shape time ≤ size time := by rw [sizeIdentity]; linarith only [dilationNonnegative', phaseValueNonnegative, momentNonnegative', translationNonnegative]
    have dilationSize : dilation time ≤ size time := by rw [sizeIdentity]; linarith only [shapeNonnegative, phaseValueNonnegative, momentNonnegative', translationNonnegative]
    have momentSize : moment time ≤ size time := by rw [sizeIdentity]; linarith only [shapeNonnegative, dilationNonnegative', phaseValueNonnegative, translationNonnegative]
    have centerSize := (geometryBounds time inside).1.trans (mul_le_mul_of_nonneg_right boundGeometry (coordinateNonnegative time))
    have actual := integrated_coefficient_finite_coordinate_scalar_majorants boundOne omegaOne epsilonNonnegative epsilonOne strainNonnegative strainSmall.le
      (div_nonneg (changed.length_pos _).le (changed.location_pos _).le) ratioOne
      (div_nonneg (changed.length_pos _).le macroNonnegative) macroRatioOne referenceNonnegative' referenceOne
      shapeNonnegative (shapeOne time inside) shapeSize dilationNonnegative' dilationSize momentNonnegative' momentSize
      centerNonnegative' centerSize rawNonnegative (norm_nonneg (leading time)) differenceNonnegative (foreignNonnegative ownRadius)
      (foreignNonnegative macroRadius) externalNonnegative (zero_le_one.trans gradedOne) boundGraded momentNonnegative boundMoment
      dilationNonnegative boundDilation phaseNonnegative boundPhase centerNonnegative boundCenter
    dsimp only [remainderUpper, momentUpper, dilationUpper, phaseUpper, centerUpper, budget]
    rw [forcingIdentity]
    exact actual
  have remainderMajorant (time : ℝ) (inside : time ∈ Ioo 0 finish) :
      ‖relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index time‖ ≤
        20 * bound ^ 2 * budget time := by
    apply (remainderBound time inside).trans
    apply le_trans _ (scalarBounds time ⟨inside.1.le, inside.2.le⟩).1
    dsimp only [remainderUpper, shape, relative, referenceSize, dilation, moment, center, raw, foreign, difference, macroRadius, ownRadius, epsilon, leading, first, second, omega, changed]
    rw [prepared.referenceIdentity]
    simp only [one_mul]
    gcongr
    exact le_add_of_nonneg_left (abs_nonneg _)
  have momentUpperContinuous : ContinuousOn momentUpper (Icc 0 finish) := by
    dsimp only [momentUpper]
    exact continuousOn_const.mul ((continuousOn_const.mul centerContinuous).add differenceContinuous |>.add
      (continuousOn_const.mul ((continuousOn_const.mul rawContinuous).add (foreignContinuous macroRadius (Or.inl rfl)))))
  have momentUpperIntegrable := momentUpperContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  obtain ⟨_, _, _, _, _, dilationUpperIntegrable, dilationPrimitive⟩ := dilationHistory
  obtain ⟨_, _, _, _, centerUpperIntegrable, centerPrimitive⟩ := centerHistory
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
  have momentContinuous : ContinuousOn moment (Icc 0 finish) := by
    intro time inside
    exact ((((prepared.toCascadeMaterialPreparedPair.paired_neutral_hasDerivAt 0 index (globalInside time inside)).sub
      (prepared.toCascadeMaterialPreparedPair.paired_neutral_hasDerivAt 1 index (globalInside time inside))).const_smul _).continuousAt.norm).continuousWithinAt
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) := by
    intro time inside
    exact (((prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 0 index (globalInside time inside)).sub
      (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 1 index (globalInside time inside))).continuousAt.abs.div_const _).continuousWithinAt
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have ownContinuous := foreignContinuous ownRadius (Or.inr rfl)
  have dilationI : IntervalIntegrable dilationUpper volume 0 finish :=
    (((((momentContinuous.add (continuousOn_const.mul centerContinuous)).add (continuousOn_const.mul rawContinuous)).add
      (continuousOn_const.mul differenceContinuous)).add (continuousOn_const.mul ownContinuous))).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have phaseI : IntervalIntegrable phaseUpper volume 0 finish :=
    ((((((continuousOn_const.mul dilationContinuous).add (continuousOn_const.mul shapeContinuous)).add
      ((momentContinuous.add centerContinuous).add shapeContinuous)).add (continuousOn_const.mul (centerContinuous.add rawContinuous))).add
      (continuousOn_const.mul differenceContinuous)).add (continuousOn_const.mul ownContinuous)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have centerI : IntervalIntegrable centerUpper volume 0 finish :=
    (((((momentContinuous.add centerContinuous).add externalC0).add (continuousOn_const.mul (centerContinuous.add rawContinuous))).add
      (continuousOn_const.mul ownContinuous))).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  refine ⟨?_, ?_⟩
  · exact retained
  ·
    refine ⟨lift, liftContinuous, polar, coordinateContinuous, coordinateInitial, forcingContinuous,
      forcingContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative, ?_⟩
    intro time inside
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have prefixSet : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]; exact prefixSubset
    let history := ∫ current in (0 : ℝ)..time, budget current
    have historyNonnegative : 0 ≤ history := intervalIntegral.integral_nonneg inside.1 (fun current _ => budgetNonnegative current)
    have compare {upper : ℝ → ℝ} {coefficient : ℝ} (integrable : IntervalIntegrable upper volume 0 finish)
        (bounded : ∀ current ∈ Icc 0 finish, upper current ≤ coefficient * budget current) :
        (∫ current in (0 : ℝ)..time, upper current) ≤ coefficient * history := by
      have actual := intervalIntegral.integral_mono_on inside.1 (integrable.mono_set prefixSet)
        ((continuousOn_const.mul (budgetContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1)
        (fun current member => bounded current (prefixSubset member))
      simpa only [intervalIntegral.integral_const_mul, history] using actual
    have momentBound : moment time ≤ 4 * bound ^ 2 * history := by
      apply le_trans _ (compare momentUpperIntegrable (fun current member => (scalarBounds current member).2.1))
      simpa only [momentUpper, intervalIntegral.integral_const_mul, moment, raw, center, difference, foreign, macroRadius, epsilon, first, second, changed,
        prepared.referenceIdentity] using momentHistory.2.2 time inside
    have dilationBound' : dilation time ≤ 7 * bound ^ 2 * history := by
      apply le_trans _ (compare dilationI (fun current member => (scalarBounds current member).2.2.1))
      simpa only [dilationUpper, dilation, moment, center, raw, difference, foreign, macroRadius, ownRadius, epsilon, omega,
        first, second, changed, one_mul, abs_div, abs_pow, sq_abs, prepared.referenceIdentity] using dilationPrimitive time inside
    have phaseBound' : phaseValue time ≤ 10 * bound ^ 2 * history := by
      apply le_trans _ (compare phaseI (fun current member => (scalarBounds current member).2.2.2.1))
      rw [show phaseValue time = |relativeCorrectedPaperPhase (phaseCorrection 1 graph) phaseLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| from congrArg abs (phaseEquality inside)]
      apply ((phasePrimitive time inside).2).trans_eq
      apply intervalIntegral.integral_congr
      intro current _
      dsimp only [phaseUpper, dilation, moment, center, raw, difference, foreign, macroRadius, ownRadius, epsilon, omega, shape, relative, first, second, changed]
      simp only [one_mul, one_add_one_eq_two, Prod.fst_sub, Prod.snd_sub, abs_div, abs_pow, sq_abs, prepared.referenceIdentity]
    have translationBound : translation time ≤ 6 * bound ^ 2 * history := by
      apply le_trans _ (compare centerI (fun current member => (scalarBounds current member).2.2.2.2))
      simpa only [translation, centerUpper, moment, center, raw, external, foreign, ownRadius, epsilon, omega, first, second, changed, one_mul,
        prepared.referenceIdentity] using centerPrimitive time inside
    let derivative := relativeStraightenedSaddleVelocity changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index
    have equation (current : ℝ) (member : current ∈ Ioo 0 time) : HasDerivAt relative (derivative current) current :=
      equations prepared.toCascadeMaterialPreparedPair path index current (subset (prefixSubset ⟨member.1.le, member.2.le⟩))
        (fun side => (pairedSmall side current (prefixSubset ⟨member.1.le, member.2.le⟩)).trans_le (min_le_left _ _))
    have derivativeBound (current : ℝ) (member : current ∈ Ioo 0 time) : ‖derivative current‖ ≤ 24 * bound ^ 2 * budget current := by
      have currentInside := prefixSubset ⟨member.1.le, member.2.le⟩
      have nonnegative := allNonnegative current
      have shapeSize : shape current ≤ size current := by rw [sizeIdentity]; linarith only [nonnegative.2.1, nonnegative.2.2.1, nonnegative.2.2.2.1, nonnegative.2.2.2.2.1]
      have omegaShape : omega * shape current ≤ budget current := by
        exact (mul_le_mul_of_nonneg_left shapeSize omegaNonnegative).trans (budgetComponents current).1
      have leadingBudget : ‖leading current‖ ≤ budget current := (budgetComponents current).2
      have growthThree : 2 * Real.sqrt 2 ≤ (3 : ℝ) := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have linearNorm : ‖(2 * Real.sqrt 2 * omega * (relative current).1, -(2 * Real.sqrt 2 * omega) * (relative current).2)‖ ≤ 3 * budget current := by
        let growth := 2 * Real.sqrt 2 * omega
        have growthNonnegative : 0 ≤ growth := mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) omegaNonnegative
        have growthShape : growth * shape current ≤ 3 * budget current := by
          calc
            _ ≤ (3 * omega) * shape current := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right growthThree omegaNonnegative) nonnegative.1
            _ = 3 * (omega * shape current) := by ring
            _ ≤ 3 * budget current := mul_le_mul_of_nonneg_left omegaShape (by norm_num)
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
        change max |growth * (relative current).1| |(-growth) * (relative current).2| ≤ 3 * budget current
        rw [abs_mul growth (relative current).1, abs_mul (-growth) (relative current).2, abs_neg]
        simp only [abs_of_nonneg growthNonnegative]
        exact max_le
          ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg (relative current).2)) growthNonnegative).trans growthShape)
          ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg (relative current).1)) growthNonnegative).trans growthShape)
      have remainder := remainderMajorant current ⟨member.1, member.2.trans_le inside.2⟩
      have triangle := (norm_add_le
        ((2 * Real.sqrt 2 * omega * (relative current).1, -(2 * Real.sqrt 2 * omega) * (relative current).2) + leading current)
        (relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index current)).trans
          (add_le_add_right (norm_add_le _ _) _)
      have identity : derivative current = (2 * Real.sqrt 2 * omega * (relative current).1, -(2 * Real.sqrt 2 * omega) * (relative current).2) + leading current +
        relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index current :=
        relativeStraightenedSaddleVelocity_eq_leading_strain _ _ _ _ _ _
      rw [identity]
      have coefficient : 4 + 20 * bound ^ 2 ≤ 24 * bound ^ 2 := by nlinarith only [boundOne, sq_nonneg (bound - 1)]
      have slack := mul_le_mul_of_nonneg_right coefficient (budgetNonnegative current)
      nlinarith only [triangle, linearNorm, leadingBudget, remainder, slack]
    have normHistory := General.norm_sub_le_integral_of_interior_derivative_majorant inside.1
      (relativeContinuous.mono prefixSubset) (continuousOn_const.mul (budgetContinuous.mono prefixSubset))
      (fun current _ => mul_nonneg (by positivity) (budgetNonnegative current)) equation derivativeBound
    rw [prepared.toCascadeMaterialPreparedPair.nonterminal_initial_straightened_difference graph coordinate index nonterminal, sub_zero,
      intervalIntegral.integral_const_mul] at normHistory
    have shapeNorm : shape time ≤ 2 * ‖relative time‖ := by
      have firstBound := norm_fst_le (relative time)
      have secondBound := norm_snd_le (relative time)
      simpa only [shape, Real.norm_eq_abs, two_mul] using add_le_add firstBound secondBound
    change ‖relative time‖ ≤ 24 * bound ^ 2 * history at normHistory
    have shapeHistory : shape time ≤ 48 * bound ^ 2 * history := by nlinarith only [shapeNorm, normHistory]
    change size time ≤ 100 * bound ^ 2 * history
    rw [sizeIdentity]
    nlinarith only [shapeHistory, dilationBound', phaseBound', momentBound, translationBound,
      mul_nonneg (sq_nonneg bound) historyNonnegative]
  
end EulerNonuniqueness.Paper

