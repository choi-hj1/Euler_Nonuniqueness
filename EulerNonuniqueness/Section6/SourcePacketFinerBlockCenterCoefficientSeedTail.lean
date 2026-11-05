import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound
import EulerNonuniqueness.Section6.FiniteExteriorWeightBound
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments
import EulerNonuniqueness.Section1.FinerCirculationSeedTail
import EulerNonuniqueness.Section3.FinitePatchRestriction

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem Scales.eventually_actual_finer_blockcenter_coefficient_seed_tail (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count,
    ∀ radius : ℝ, 0 ≤ radius → radius ≤ ({scales with frequency := frequency} : Scales).location (receiver.val + 1) / (100000 * 96) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.referenceWitness.trajectory.movingFamily
    let second := prepared.trajectory.movingFamily
    let difference := fun source power =>
      (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter second.patchMotion current receiver) radius (power + 1) time -
        (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter first.patchMotion current receiver) radius (power + 1) time
    (∀ source : Fin count, receiver.val + 2 ≤ source.val →
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖difference source power‖)) ∧
    (∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
      ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖difference source power‖) ≤
        tolerance * changed.seed (receiver.val + 1) := by
  filter_upwards [scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_finer_circulation_seed_tail ratioBound alphaPositive ratioPower 2 0
      (tolerance := tolerance * Real.pi / 442368) (by positivity),
    eventually_ge_atTop (1 : ℝ)]
    with frequency clearance tail frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let coefficient := fun (family : FiniteMovingPatchFamily (count * 4)) source power =>
    (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
      (fun current => quadrupoleCenter family.patchMotion current receiver) radius (power + 1) time
  let difference := fun source power => coefficient second source power - coefficient first source power
  let selected := Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val)
  let term := fun index : ℕ => changed.circulation (receiver.val + 3 + index) /
    changed.location (receiver.val + 3 + index) ^ 2
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have referenceEvolution : FinitePatchEvolution changed first.patchMotion path.stop :=
    prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith only [path.stopBound])
  have termNonnegative (index : ℕ) : 0 ≤ term index :=
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have termSummable : Summable term := by
    have shifted := (changed.circulation_location_summable frequencyOne ratioBound alphaPositive 2).comp_injective
      (show Function.Injective (fun index : ℕ => receiver.val + 2 + index) from
        fun _ _ equality => Nat.add_left_cancel equality)
    simpa only [term, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using shifted
  have tailInjective : Set.InjOn (fun source : Fin count => source.val - (receiver.val + 2)) selected := by
    intro left leftMember right rightMember equality
    have leftBound := (Finset.mem_filter.mp leftMember).2
    have rightBound := (Finset.mem_filter.mp rightMember).2
    dsimp only at equality
    apply Fin.ext
    omega
  have finiteTail : (∑ source ∈ selected, term (source.val - (receiver.val + 2))) ≤ ∑' index, term index := by
    rw [← Finset.sum_image tailInjective]
    exact termSummable.sum_le_tsum _ (fun index _ => termNonnegative index)
  have scalarTail : (∑' index, term index) ≤
      tolerance * Real.pi / 442368 * changed.seed (receiver.val + 1) := by
    simpa only [pow_zero, one_mul, term, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tail (receiver.val + 1)
  have individual (source : Fin count) (member : source ∈ selected) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖difference source power‖) ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖difference source power‖) ≤
        (442368 / Real.pi) * term (source.val - (receiver.val + 2)) := by
    have finer := (Finset.mem_filter.mp member).2
    have different : receiver ≠ source := by intro same; subst source; omega
    have differentIndices : receiver.val + 1 ≠ source.val + 1 :=
      fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let distance := gap / 8
    have gapPositive : 0 < gap := changed.location_distance_pos differentIndices
    have distancePositive : 0 < distance := div_pos gapPositive (by norm_num)
    have sourcePositive := changed.location_pos (source.val + 1)
    have receiverPositive := changed.location_pos (receiver.val + 1)
    have circulationNonnegative := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    have spacing := changed.location_sum_le_three_distance differentIndices
    have sourceMember : source ∈ Finset.univ.erase receiver :=
      Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
    have sourceClearance := clearance count phase dipoleAngle prepared path time inside receiver
    have firstSeparated : ∀ patch position, position ∈ first.patchMotion.domain time source patch →
        distance ≤ ‖quadrupoleCenter first.patchMotion time receiver - position‖ :=
      sourceClearance.1 source sourceMember
    have secondSeparated : ∀ patch position, position ∈ second.patchMotion.domain time source patch →
        distance ≤ ‖quadrupoleCenter second.patchMotion time receiver - position‖ :=
      sourceClearance.2 source sourceMember
    let quotient := 96 * radius / distance
    have quotientNonnegative : 0 ≤ quotient := by dsimp only [quotient]; positivity
    have quotientSmall : quotient ≤ 1 / 2 := by
      apply (div_le_iff₀ distancePositive).mpr
      dsimp only [distance]
      nlinarith only [radiusSmall, spacing, sourcePositive, gapPositive]
    have quotientOne : quotient < 1 := quotientSmall.trans_lt (by norm_num)
    have oneFamily (family : FiniteMovingPatchFamily (count * 4))
        (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
          patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4)
        (evolution : FinitePatchEvolution changed family.patchMotion path.stop)
        (separated : ∀ patch position, position ∈ family.patchMotion.domain time source patch →
          distance ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖) :
        Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient family source power‖) ∧
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient family source power‖) ≤
          384 * changed.circulation (source.val + 1) / (Real.pi * distance ^ 2) := by
      have fieldIdentity : (family.quadrupoleSubfamily source).subfamilyVorticity Finset.univ time =
          quadrupoleDensity changed family.patchMotion time source := by
        funext position
        apply Finset.sum_congr rfl
        intro patch _
        change ((family.patch (finProdFinEquiv (source, patch))).domain time).indicator
          (fun _ => family.density (finProdFinEquiv (source, patch))) position = _
        rw [densities]
        rfl
      have support := (family.quadrupoleSubfamily source).subfamily_support_separated Finset.univ
        (quadrupoleCenter family.patchMotion time receiver) time distance (fun patch _ => separated patch)
      rw [fieldIdentity] at support
      have weightBound : (∫ position, inverseSquareVorticityWeight
          (quadrupoleDensity changed family.patchMotion time source)
          (quadrupoleCenter family.patchMotion time receiver) position) ≤
          4 * changed.circulation (source.val + 1) / distance ^ 2 := by
        have actual := integral_inverseSquareVorticityWeight_le_mass
          (evolution.quadrupoleDensity_integrable inside source) _ distancePositive support
        have mass := evolution.quadrupoleDensity_integral_abs_le inside amplitudePositive frequencyPositive ratioPositive source
        exact actual.trans ((mul_le_mul_of_nonneg_left mass (sq_nonneg distance⁻¹)).trans_eq
          (by simp only [div_eq_mul_inv, inv_pow]; ring))
      let constant := 96 * ((4 * changed.circulation (source.val + 1) / distance ^ 2) / (2 * Real.pi))
      have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
      have bound (power : ℕ) : (96 : ℝ) ^ (power + 1) * ‖coefficient family source power‖ ≤
          quotient ^ power * constant := by
        have identity := (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_eq_vorticityCoefficient Finset.univ
          (fun current => quadrupoleCenter family.patchMotion current receiver) radius time power distancePositive
          (fun patch _ => separated patch)
        rw [fieldIdentity] at identity
        have actual := norm_exteriorVorticityCoefficient_le (evolution.quadrupoleDensity_integrable inside source)
          (quadrupoleCenter family.patchMotion time receiver) radiusNonnegative distancePositive support power
        have upper := actual.trans (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right weightBound (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
          (pow_nonneg (div_nonneg radiusNonnegative distancePositive.le) power))
        dsimp only [coefficient]
        rw [identity]
        have weighted := mul_le_mul_of_nonneg_left upper (show (0 : ℝ) ≤ 96 ^ (power + 1) by positivity)
        convert weighted using 1
        dsimp only [quotient, constant]
        rw [show 96 * radius / distance = 96 * (radius / distance) by ring, mul_pow, pow_succ]
        ring
      have geometric := (summable_geometric_of_lt_one quotientNonnegative quotientOne).mul_right constant
      have summable := Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _)) bound geometric
      refine ⟨summable, ?_⟩
      have actual := summable.tsum_le_tsum bound geometric
      rw [tsum_mul_right, tsum_geometric_of_lt_one quotientNonnegative quotientOne] at actual
      have inverseBound : (1 - quotient)⁻¹ ≤ 2 := by
        rw [← one_div]
        apply (div_le_iff₀ (show 0 < 1 - quotient by linarith only [quotientOne])).mpr
        linarith only [quotientSmall]
      exact actual.trans ((mul_le_mul_of_nonneg_right inverseBound constantNonnegative).trans_eq
        (by dsimp only [constant]; ring))
    obtain ⟨firstSummable, firstBound⟩ := oneFamily first prepared.referenceWitness.densityIdentity referenceEvolution firstSeparated
    obtain ⟨secondSummable, secondBound⟩ := oneFamily second prepared.densityIdentity path.evolution secondSeparated
    have pairedPointwise (power : ℕ) : (96 : ℝ) ^ (power + 1) * ‖difference source power‖ ≤
        (96 : ℝ) ^ (power + 1) * ‖coefficient second source power‖ +
          (96 : ℝ) ^ (power + 1) * ‖coefficient first source power‖ := by
      exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (show (0 : ℝ) ≤ 96 ^ (power + 1) by positivity)).trans_eq
        (by ring)
    have pairedSummable := Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
      pairedPointwise (secondSummable.add firstSummable)
    refine ⟨pairedSummable, ?_⟩
    have pairedBound := pairedSummable.tsum_le_tsum pairedPointwise (secondSummable.add firstSummable)
    rw [secondSummable.tsum_add firstSummable] at pairedBound
    have coarse : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖difference source power‖) ≤
        49152 * changed.circulation (source.val + 1) / (Real.pi * gap ^ 2) :=
      pairedBound.trans ((add_le_add secondBound firstBound).trans_eq (by dsimp only [distance]; ring))
    have inverseGap : 1 / gap ^ 2 ≤ 9 / changed.location (source.val + 1) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos gapPositive) (sq_pos_of_pos sourcePositive)).mpr
      nlinarith only [spacing, receiverPositive, sourcePositive, gapPositive]
    have actual := mul_le_mul_of_nonneg_left inverseGap
      (show 0 ≤ 49152 * changed.circulation (source.val + 1) / Real.pi by positivity)
    have indexIdentity : receiver.val + 3 + (source.val - (receiver.val + 2)) = source.val + 1 := by omega
    apply coarse.trans
    dsimp only [term]
    rw [indexIdentity]
    convert actual using 1 <;> ring
  refine ⟨?_, ?_⟩
  · intro source finer
    exact (individual source (Finset.mem_filter.mpr ⟨Finset.mem_univ _, finer⟩)).1
  · have finiteBound := Finset.sum_le_sum (fun source member => (individual source member).2)
    rw [← Finset.mul_sum] at finiteBound
    have weightedFinite := mul_le_mul_of_nonneg_left finiteTail (show (0 : ℝ) ≤ 442368 / Real.pi by positivity)
    have weightedTail := mul_le_mul_of_nonneg_left scalarTail (show (0 : ℝ) ≤ 442368 / Real.pi by positivity)
    exact (finiteBound.trans weightedFinite).trans (weightedTail.trans_eq (by field_simp; ring))

end EulerNonuniqueness.Paper

