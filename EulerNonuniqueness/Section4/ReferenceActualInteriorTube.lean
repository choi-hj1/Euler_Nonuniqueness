import EulerNonuniqueness.Section4.ReferenceComputedSaddleBound
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity
import EulerNonuniqueness.Section4.ReferenceInitialShapeCoordinates
import EulerNonuniqueness.Section5.ReferenceOutwardFaces

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_interior_tube :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales},
      ∀ {horizon memory bound threshold : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 ≤ horizon → 0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      0 ≤ memory → 0 ≤ bound → scales.hessian ≤ 1 →
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks scales family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
      ∀ (index : Fin count),
      (∀ time ∈ Icc 0 horizon, ReferenceCentroidFieldGeometry scales family.patchMotion time index) →
      (∀ time ∈ Icc 0 horizon, ∀ patch : Fin 4,
        time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
          (family.patch (finProdFinEquiv (index, patch))).finalTime) →
      (∀ time ∈ Icc 0 horizon, ∀ patch label,
        (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
          biotSavart (Paper.patchVorticity scales family.patchMotion time)
            ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) →
      ∀ (deformation : ℝ → ℝ),
      (∀ time ∈ Icc 0 horizon, ∀ patch,
        BoundaryCloseToCircle scales family.patchMotion time index patch (deformation time)) →
      (∀ time ∈ Icc 0 horizon, 0 ≤ deformation time) →
      (∀ time ∈ Icc 0 horizon, deformation time ≤ 1 / 16) →
      (∀ time ∈ Icc 0 horizon, deformation time ≤ bound / scales.omega (index.val + 1) ^ 2) →
      scales.length (index.val + 1) ≤ 1 →
      (∀ time ∈ Icc 0 horizon, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 horizon, diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 horizon, ‖centroidAsymmetry family.patchMotion time index‖ ≤
        memory * scales.length (index.val + 1) ^ 2) →
      scales.length (index.val + 1) < momentRadius / (8 * (memory + 1)) →
      (∀ time ∈ Icc 0 horizon, 0 < (negativeHalfDiagonal family.patchMotion time index /
        positiveHalfDiagonal family.patchMotion time index).im) →
      (∀ time ∈ Icc 0 horizon, |unstableShape family.patchMotion time index| ≤ radius ∧
        |stableShape family.patchMotion time index| ≤ radius) →
      (∀ time ∈ Icc 0 horizon, |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤
        2 * (4 * referenceShapeForcingBudget scales (index.val + 1) internal memory bound /
          scales.omega (index.val + 1) + radius * Real.exp (-(scales.omega (index.val + 1) / 2) * (horizon - time)))) ∧
      (referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
          scales.omega (index.val + 1) * radius / 16 →
        ∀ time ∈ Icc 0 horizon,
        (unstableShape family.patchMotion time index = radius → scales.omega (index.val + 1) * radius / 2 ≤
          (referencePointShapeVelocity scales family.patchMotion time index).1) ∧
        (unstableShape family.patchMotion time index = -radius → (referencePointShapeVelocity scales family.patchMotion time index).1 ≤
          -(scales.omega (index.val + 1) * radius / 2)) ∧
        (stableShape family.patchMotion time index = radius → (referencePointShapeVelocity scales family.patchMotion time index).2 ≤
          -(scales.omega (index.val + 1) * radius / 2)) ∧
        (stableShape family.patchMotion time index = -radius → scales.omega (index.val + 1) * radius / 2 ≤
          (referencePointShapeVelocity scales family.patchMotion time index).2)) := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, quadratic, quadraticNonnegative,
    shapeRadius, shapeRadiusPositive, estimate⟩ := exists_uniform_computed_reference_saddle_bound
  let radius := min (min (shapeRadius / 4) (1 / (32 * (quadratic + 1)))) (1 / 8)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusSmall : radius ≤ 1 / 8 := min_le_right _ _
  have shapeSmall : radius ≤ shapeRadius / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have quadraticSmall : radius ≤ 1 / (32 * (quadratic + 1)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have scaled : 32 * (quadratic + 1) * radius ≤ 1 := by
    have divided := (le_div_iff₀ (by positivity : 0 < 32 * (quadratic + 1))).mp quadraticSmall
    nlinarith only [divided]
  have scalarCost : 4 * quadratic * radius ^ 2 ≤ radius / 8 := by
    have product := mul_le_mul_of_nonneg_right scaled radiusPositive.le
    nlinarith only [product, sq_nonneg radius]
  have quadraticRadius : 16 * quadratic * radius ≤ 1 := by
    nlinarith only [scaled, radiusPositive.le]
  refine ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, radius, radiusPositive, radiusSmall, ?_⟩
  intro count family scales horizon memory bound threshold evolution horizonNonnegative amplitudePositive frequencyBound ratioBound
    alphaPositive memoryNonnegative boundNonnegative hessianBound phase unstable initial thresholdSmall index geometry inside material
    deformation control nonnegative small deformationBound lengthBound differenceLower differenceUpper asymmetryBound lengthSmall
    upper bootstrap
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have differencePositive (time : ℝ) (member : time ∈ Icc 0 horizon) :
      0 < diagonalDifference family.patchMotion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le (differenceLower time member)
  have chartSmall (time : ℝ) (member : time ∈ Icc 0 horizon) :
      |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| < shapeRadius := by
    have boundAt := bootstrap time member
    linarith
  have paperSmall (time : ℝ) (member : time ∈ Icc 0 horizon) :
      |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4 := by
    have boundAt := bootstrap time member
    linarith
  have actualBound (time : ℝ) (member : time ∈ Icc 0 horizon) := estimate evolution member amplitudePositive
    frequencyBound ratioBound alphaPositive index (geometry time member) (control time member) (nonnegative time member)
    (small time member) memoryNonnegative boundNonnegative (deformationBound time member) lengthBound hessianBound
    (differenceLower time member) (differenceUpper time member) (asymmetryBound time member) lengthSmall
    (upper time member) (chartSmall time member)
  have equation (time : ℝ) (member : time ∈ Icc 0 horizon) :=
    family.centroid_paper_shape_hasDerivAt_of_upper evolution member index (inside time member)
      (material time member) (upper time member) (paperSmall time member)
  let rate := fun time => referencePointShapeRate scales family.patchMotion time index
  let unstableForce := fun time => (referencePointShapeVelocity scales family.patchMotion time index).1 -
    rate time * unstableShape family.patchMotion time index
  let stableForce := fun time => (referencePointShapeVelocity scales family.patchMotion time index).2 +
    rate time * stableShape family.patchMotion time index
  have shapeContinuous : ContinuousOn (fun time => (unstableShape family.patchMotion time index,
      stableShape family.patchMotion time index)) (Icc 0 horizon) := by
    intro time member
    exact (equation time member).continuousAt.continuousWithinAt
  have differenceContinuous : ContinuousOn (fun time => diagonalDifference family.patchMotion time index) (Icc 0 horizon) := by
    intro time member
    obtain ⟨positiveSmooth, negativeSmooth⟩ := family.halfDiagonals_contDiffAt index (inside time member)
    have positiveNorm : ContDiffAt ℝ 1 (fun current => ‖positiveHalfDiagonal family.patchMotion current index‖ ^ 2) time :=
      (contDiff_norm_sq ℝ).contDiffAt.comp time positiveSmooth
    have negativeNorm : ContDiffAt ℝ 1 (fun current => ‖negativeHalfDiagonal family.patchMotion current index‖ ^ 2) time :=
      (contDiff_norm_sq ℝ).contDiffAt.comp time negativeSmooth
    exact (positiveNorm.sub negativeNorm).continuousAt.continuousWithinAt
  have rateContinuous : ContinuousOn rate (Icc 0 horizon) :=
    continuousOn_const.mul (continuousOn_const.div differenceContinuous
      (fun time member => (differencePositive time member).ne'))
  have velocityContinuous := family.referencePointShapeVelocity_continuousOn evolution index inside material upper paperSmall
  have unstableForceContinuous : ContinuousOn unstableForce (Icc 0 horizon) :=
    velocityContinuous.fst.sub (rateContinuous.mul shapeContinuous.fst)
  have stableForceContinuous : ContinuousOn stableForce (Icc 0 horizon) :=
    velocityContinuous.snd.add (rateContinuous.mul shapeContinuous.snd)
  have forcingNonnegative : 0 ≤ referenceShapeForcingBudget scales (index.val + 1) internal memory bound := by
    have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
      div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    dsimp only [referenceShapeForcingBudget]
    positivity
  have stableInitial : stableShape family.patchMotion 0 index = 0 := by
    exact congrArg Prod.snd (evolution.reference_initial_paper_shape horizonNonnegative amplitudePositive frequencyPositive
      ratioPositive initial thresholdSmall index).2
  constructor
  · suffices tube : ∀ time ∈ Icc 0 horizon,
        |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤
          2 * (2 * (2 * referenceShapeForcingBudget scales (index.val + 1) internal memory bound) /
            scales.omega (index.val + 1) + radius * Real.exp (-(scales.omega (index.val + 1) / 2) * (horizon - time))) by
      intro time member
      convert tube time member using 1 <;> ring
    apply EulerNonuniqueness.Section5.reference_interior_tube_of_actual_equations_on_Icc
      (rate := rate) (unstableForcing := unstableForce) (stableForcing := stableForce)
      (quadratic := quadratic * scales.omega (index.val + 1))
      (forcingBound := 2 * referenceShapeForcingBudget scales (index.val + 1) internal memory bound)
      omegaPositive horizonNonnegative radiusPositive (by positivity) (mul_nonneg quadraticNonnegative omegaPositive.le)
    · have multiplied := mul_le_mul_of_nonneg_right quadraticRadius omegaPositive.le
      convert multiplied using 1 <;> ring
    · exact rateContinuous
    · exact shapeContinuous.fst
    · exact shapeContinuous.snd
    · exact unstableForceContinuous
    · exact stableForceContinuous
    · intro time member
      exact (actualBound time member).1
    · intro time member
      have velocityIdentity : rate time * unstableShape family.patchMotion time index + unstableForce time =
          (referencePointShapeVelocity scales family.patchMotion time index).1 := by dsimp only [unstableForce]; ring
      rw [velocityIdentity]
      simpa only [ContinuousLinearMap.coe_fst', Function.comp_def] using
        (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time (equation time member)
    · intro time member
      have velocityIdentity : -rate time * stableShape family.patchMotion time index + stableForce time =
          (referencePointShapeVelocity scales family.patchMotion time index).2 := by dsimp only [stableForce]; ring
      rw [velocityIdentity]
      simpa only [ContinuousLinearMap.coe_snd', Function.comp_def] using
        (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time (equation time member)
    · exact stableInitial
    · exact bootstrap
    · intro time member
      exact (actualBound time member).2
  · intro forcingSmall time member
    have numerical : 4 * (quadratic * scales.omega (index.val + 1)) * radius ^ 2 +
        2 * referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
        scales.omega (index.val + 1) * radius / 2 := by
      have multiplied := mul_le_mul_of_nonneg_left scalarCost omegaPositive.le
      nlinarith only [multiplied, forcingSmall, mul_pos omegaPositive radiusPositive]
    have faces := EulerNonuniqueness.Section5.reference_saddle_face_signs radiusPositive.le
      (mul_nonneg quadraticNonnegative omegaPositive.le) (actualBound time member).1
      (bootstrap time member).1 (bootstrap time member).2 (actualBound time member).2 numerical
    have unstableIdentity : rate time * unstableShape family.patchMotion time index + unstableForce time =
        (referencePointShapeVelocity scales family.patchMotion time index).1 := by dsimp only [unstableForce]; ring
    have stableIdentity : -rate time * stableShape family.patchMotion time index + stableForce time =
        (referencePointShapeVelocity scales family.patchMotion time index).2 := by dsimp only [stableForce]; ring
    change (_ → _ ≤ rate time * unstableShape family.patchMotion time index + unstableForce time) ∧
      (_ → rate time * unstableShape family.patchMotion time index + unstableForce time ≤ _) ∧
      (_ → -rate time * stableShape family.patchMotion time index + stableForce time ≤ _) ∧
      (_ → _ ≤ -rate time * stableShape family.patchMotion time index + stableForce time) at faces
    rwa [unstableIdentity, stableIdentity] at faces

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
