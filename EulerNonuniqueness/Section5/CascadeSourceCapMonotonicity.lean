import EulerNonuniqueness.Section5.CascadeSourcePreparedPair

noncomputable section

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant smaller larger : ℝ} {count : ℕ}

def enlargeCap
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (bound : smaller ≤ larger) :
    CascadeSourcePreparedPair larger scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count :=
  {prepared.toCascadeMaterialPreparedPair with
    referenceShapeCap := fun time inside label => (prepared.referenceShapeCap time inside label).trans_le bound
    monitorCap := prepared.monitorCap.trans bound}

theorem enlargeCap_material_identity
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (bound : smaller ≤ larger) :
    (prepared.enlargeCap bound).toCascadeMaterialPreparedPair = prepared.toCascadeMaterialPreparedPair := rfl

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
