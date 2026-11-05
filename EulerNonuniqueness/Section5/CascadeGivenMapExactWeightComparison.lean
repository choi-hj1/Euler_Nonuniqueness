import EulerNonuniqueness.Section5.CascadeIntegratedNonlinearCoefficient
import EulerNonuniqueness.General.SaddleExactWeightComparison

noncomputable section

open Set MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem CascadeSourcePreparedPair.givenMap_exact_weight_comparison
    {rawCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (graph coordinate : ℝ → ℝ) (index : Fin count)
    {stableConstant dilationConstant chartConstant tolerance finish : ℝ}
    (stableNonnegative : 0 ≤ stableConstant) (_dilationNonnegative : 0 ≤ dilationConstant)
    (chartNonnegative : 0 ≤ chartConstant) (referenceNonnegative : 0 ≤ referenceConstant)
    (toleranceNonnegative : 0 ≤ tolerance) (factorPositive : 0 < factor)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (finishNonnegative : 0 ≤ finish) :
      let changed : Scales := scales
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
        (tolerance + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * center time +
        dilationConstant * omega * epsilon * raw time + dilationConstant * difference time +
        dilationConstant * epsilon * ∑ patch : Fin 4, foreign patch time
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
      let actionCost := 2 * omega * indexedReferenceSize * finish +
        2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
        ∫ time in (0 : ℝ)..finish, forcing time
      let feedback := fun time => stableConstant * omega * coefficient time
      let additive := fun time => forcing time - |(leading time).2| +
        stableConstant * omega * indexedReferenceSize * dilation time
      let drive := fun time => ‖leading time‖ + additive time
      let action := stableConstant * actionCost
      let weighted := fun (function : ℝ → ℝ) time => ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * current) * function current
      let error := fun time => 2 * action * Real.exp (2 * action) * weighted drive time + weighted additive time
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
          ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * upper time)) →
      ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn leading (Icc 0 finish) ∧
      ContinuousOn remainder (Icc 0 finish) ∧ ContinuousOn shape (Icc 0 finish) ∧
      ContinuousOn feedback (Icc 0 finish) ∧ ContinuousOn additive (Icc 0 finish) ∧ ContinuousOn drive (Icc 0 finish) ∧
      IntervalIntegrable dilationMajorant volume 0 finish ∧ IntervalIntegrable forcing volume 0 finish ∧
      IntervalIntegrable feedback volume 0 finish ∧
      (∫ time in (0 : ℝ)..finish, feedback time) ≤ action ∧
      (∀ time, 0 ≤ feedback time ∧ 0 ≤ additive time ∧ 0 ≤ drive time) ∧
      relative 0 = 0 ∧
      ∀ time ∈ Icc 0 finish,
        IntervalIntegrable (fun current => Real.exp (-growth * current) * shape current) volume 0 time ∧
        IntervalIntegrable (fun current => Real.exp (-growth * current) * drive current) volume 0 time ∧
        IntervalIntegrable (fun current => Real.exp (-growth * current) * ‖remainder current‖) volume 0 time ∧
        IntervalIntegrable (fun current => Real.exp (-growth * current) * additive current) volume 0 time ∧
        IntervalIntegrable (fun current => Real.exp (-growth * current) * (leading current).1) volume 0 time ∧
        Real.exp (-growth * time) * shape time ≤
          2 * Real.exp (2 * stableConstant * omega * (∫ current in (0 : ℝ)..time, coefficient current)) * weighted drive time ∧
        Real.exp (-growth * time) * shape time ≤ 2 * Real.exp (2 * action) * weighted drive time ∧
        weighted (fun current => ‖remainder current‖) time ≤ error time ∧
        weighted (fun current => (leading current).1) time - error time ≤
          Real.exp (-growth * time) * (relative time).1 := by
  dsimp only
  intro data
  let changed : Scales := scales
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
    (tolerance + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * center time +
    dilationConstant * omega * epsilon * raw time + dilationConstant * difference time +
    dilationConstant * epsilon * ∑ patch : Fin 4, foreign patch time
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
  let actionCost := 2 * omega * indexedReferenceSize * finish +
    2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
    ∫ time in (0 : ℝ)..finish, forcing time
  let feedback := fun time => stableConstant * omega * coefficient time
  let additive := fun time => forcing time - |(leading time).2| +
    stableConstant * omega * indexedReferenceSize * dilation time
  let drive := fun time => ‖leading time‖ + additive time
  let action := stableConstant * actionCost
  let weighted := fun (function : ℝ → ℝ) time => ∫ current in (0 : ℝ)..time,
    Real.exp (-growth * current) * function current
  let error := fun time => 2 * action * Real.exp (2 * action) * weighted drive time + weighted additive time

  obtain ⟨coefficientContinuous, dilationMajorantContinuous, forcingContinuous, coefficientIntegrable, _, forcingIntegrable,
    actionBound, growthPositive, relativeContinuous, leadingContinuous, remainderContinuous, _, _, remainderBound, histories, _⟩ := data
  change ContinuousOn coefficient (Icc 0 finish) at coefficientContinuous
  change ContinuousOn dilationMajorant (Icc 0 finish) at dilationMajorantContinuous
  change ContinuousOn forcing (Icc 0 finish) at forcingContinuous
  change IntervalIntegrable coefficient volume 0 finish at coefficientIntegrable
  change IntervalIntegrable forcing volume 0 finish at forcingIntegrable
  change omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤ actionCost at actionBound
  change 0 < growth at growthPositive
  change ContinuousOn relative (Icc 0 finish) at relativeContinuous
  change ContinuousOn leading (Icc 0 finish) at leadingContinuous
  change ContinuousOn remainder (Icc 0 finish) at remainderContinuous
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) :=
    ((coefficientContinuous.sub continuousOn_const).sub relativeContinuous.snd.abs).congr (fun time _ => by
      dsimp only [coefficient]
      ring_nf)
  have feedbackContinuous : ContinuousOn feedback (Icc 0 finish) := continuousOn_const.mul coefficientContinuous
  have additiveContinuous : ContinuousOn additive (Icc 0 finish) :=
    (forcingContinuous.sub leadingContinuous.snd.abs).add (continuousOn_const.mul dilationContinuous)
  have driveContinuous : ContinuousOn drive (Icc 0 finish) := leadingContinuous.norm.add additiveContinuous
  have omegaPositive : 0 < omega := scales.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := scales.length_pos _
  have locationPositive := scales.location_pos (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have referenceNonnegativeActual : 0 ≤ indexedReferenceSize := by
    dsimp only [indexedReferenceSize]
    exact mul_nonneg (mul_nonneg chartNonnegative referenceNonnegative)
      (add_nonneg (div_nonneg (add_nonneg strainNonnegative (sq_nonneg _)) omegaPositive.le)
        (pow_nonneg (inv_nonneg.mpr omegaPositive.le) _))
  have dilationNonnegativeActual (time : ℝ) : 0 ≤ dilation time := div_nonneg (abs_nonneg _) (sq_nonneg _)
  have coefficientNonnegative (time : ℝ) : 0 ≤ coefficient time :=
    add_nonneg (add_nonneg referenceNonnegativeActual (dilationNonnegativeActual time)) (abs_nonneg _)
  have feedbackNonnegative (time : ℝ) : 0 ≤ feedback time :=
    mul_nonneg (mul_nonneg stableNonnegative omegaPositive.le) (coefficientNonnegative time)
  have additiveNonnegative (time : ℝ) : 0 ≤ additive time := by
    have centerNonnegative : 0 ≤ center time := by
      dsimp only [center, CascadeSourcePreparedPair.rawSourceCenteredState]
      exact div_nonneg (norm_nonneg _) lengthPositive.le
    have rawNonnegative : 0 ≤ raw time := by
      dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    have differenceNonnegative : 0 ≤ difference time := tsum_nonneg fun power => norm_nonneg _
    have foreignNonnegative : 0 ≤ ∑ patch : Fin 4, foreign patch time :=
      Finset.sum_nonneg fun patch _ => tsum_nonneg fun power => mul_nonneg (by positivity) (norm_nonneg _)
    have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have centerRadiusPositive : 0 < centerRadius := mul_pos (div_pos factorPositive (by norm_num)) locationPositive
    have identity : additive time = tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (scales.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖ +
        stableConstant * omega * indexedReferenceSize * dilation time := by
      dsimp only [additive, forcing]
      ring
    rw [identity]
    dsimp only [moment, shape]
    positivity
  have driveNonnegative (time : ℝ) : 0 ≤ drive time := add_nonneg (norm_nonneg _) (additiveNonnegative time)
  have feedbackAction : (∫ time in (0 : ℝ)..finish, feedback time) ≤ action := by
    have scaled := mul_le_mul_of_nonneg_left actionBound stableNonnegative
    dsimp only [feedback, action]
    rw [intervalIntegral.integral_const_mul]
    (convert scaled using 1); ring
  have unstableHistory (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Real.exp (-growth * time) * (relative time).1 =
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current + remainder current).1 := by
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have exponential : Continuous (fun current : ℝ => Real.exp (-growth * current)) := by fun_prop
    have firstIntegrable := (exponential.continuousOn.mul (leadingContinuous.fst.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have secondIntegrable := (exponential.continuousOn.mul (remainderContinuous.fst.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    rw [(histories time inside).2.1, ← intervalIntegral.integral_add firstIntegrable secondIntegrable]
    apply intervalIntegral.integral_congr
    intro current _
    simp only [Prod.fst_add, mul_add]
  have actualRemainderBound (time : ℝ) (inside : time ∈ Ioo 0 finish) :
      ‖remainder time‖ ≤ feedback time * shape time + additive time := by
    have identity : upper time = feedback time * shape time + additive time := by
      dsimp only [upper, feedback, graded, additive, forcing]
      ring
    exact (remainderBound time inside).trans_eq identity
  have comparison := General.saddle_exact_weight_shape_remainder_comparison_on_Icc
    growthPositive.le finishNonnegative relativeContinuous leadingContinuous remainderContinuous
    feedbackContinuous additiveContinuous (fun time _ => feedbackNonnegative time) (fun time _ => additiveNonnegative time)
    unstableHistory (fun time inside => (histories time inside).2.2.1) actualRemainderBound feedbackAction
  refine ⟨relativeContinuous, leadingContinuous, remainderContinuous, shapeContinuous, feedbackContinuous,
    additiveContinuous, driveContinuous, dilationMajorantContinuous.intervalIntegrable_of_Icc finishNonnegative,
    forcingIntegrable, comparison.2.1, feedbackAction,
    (fun time => ⟨feedbackNonnegative time, additiveNonnegative time, driveNonnegative time⟩), comparison.1, ?_⟩
  intro time inside
  obtain ⟨shapeIntegrable, driveIntegrable, remainderIntegrable, additiveIntegrable, leadingIntegrable,
    prefixUpper, uniformUpper, remainderEstimate, signedLower⟩ := comparison.2.2 time inside
  have prefixIdentity : (∫ current in (0 : ℝ)..time, feedback current) =
      stableConstant * omega * ∫ current in (0 : ℝ)..time, coefficient current := by
    dsimp only [feedback]
    exact intervalIntegral.integral_const_mul _ _
  have prefixUpperNormalized : Real.exp (-growth * time) * shape time ≤
      2 * Real.exp (2 * stableConstant * omega * (∫ current in (0 : ℝ)..time, coefficient current)) * weighted drive time := by
    simpa only [prefixIdentity, mul_assoc] using prefixUpper
  exact ⟨shapeIntegrable, driveIntegrable, remainderIntegrable, additiveIntegrable, leadingIntegrable,
    prefixUpperNormalized, uniformUpper, remainderEstimate, signedLower⟩

end EulerNonuniqueness.Paper
