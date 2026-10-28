import OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding

/-! # Rational Unit Evaluation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation.Constructions

noncomputable section

/-! Evaluate an actual rational-function local power identity on the common
unit domain, including negative exponents and its forced nonzero parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  {g : X.carrier.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.carrier g)

def referenceLocus (U : X.carrier.Opens) : Set (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :=
  {y | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ D.domain}

def referenceLocusIntersectionMap (U : X.carrier.Opens) :
    C(referenceLocus X D U, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U ⊓ D.domain)) :=
  ⟨fun y => ⟨y.val.val, y.val.property, y.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def referenceUnitOnIntersection (U : X.carrier.Opens) : Γ(X.carrier, U ⊓ D.domain)ˣ :=
  Units.map (X.carrier.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom D.unit

def referenceEquation (U : X.carrier.Opens) : C(referenceLocus X D U, ℂ) :=
  (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (U ⊓ D.domain) (referenceUnitOnIntersection X D U)).comp
    (referenceLocusIntersectionMap X D U)

theorem referenceEquation_ne_zero (U : X.carrier.Opens) (y : referenceLocus X D U) :
    referenceEquation X D U y ≠ 0 :=
  DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X (U ⊓ D.domain) (referenceUnitOnIntersection X D U) _

variable (U : X.carrier.Opens) [Nonempty U]
  (p : Γ(X.carrier, U)) (v : Γ(X.carrier, U)ˣ) (m : ℤ)
  (he : g = X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m)

include he

theorem referenceEquation_power (y : referenceLocus X D U)
    (hp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0) :
    referenceEquation X D U y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (v : Γ(X.carrier, U)) y.val *
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val) ^ m := by
  let W := U ⊓ D.domain
  let z : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X W := referenceLocusIntersectionMap X D U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  let t : Γ(X.carrier, W)ˣ := referenceUnitOnIntersection X D U
  let q : Γ(X.carrier, W) := X.carrier.presheaf.map (homOfLE inf_le_left).op p
  let w : Γ(X.carrier, W) := X.carrier.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.carrier, U))
  have hfield : X.carrier.germToFunctionField W t =
      X.carrier.germToFunctionField W w * (X.carrier.germToFunctionField W q) ^ m := by
    change X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE inf_le_right).op (D.unit : Γ(X.carrier, D.domain))) =
      X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.carrier, U))) *
        (X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE inf_le_left).op p)) ^ m
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, D.represents]
    exact he
  have hp' : HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation.sectionEvaluationHom (X := X) W z q ≠ 0 := by
    change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE inf_le_left).op p) z ≠ 0
    rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict]
    exact hp
  have h := HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.evaluate_integer_power_relation (X.carrier.germToFunctionField W).hom
    (X.carrier.germToFunctionField_injective W) (HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation.sectionEvaluationHom (X := X) W z)
    t w q m hfield hp'
  change referenceEquation X D U y =
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.carrier, U))) z *
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE inf_le_left).op p) z) ^ m at h
  rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict] at h
  exact h

theorem referenceParameter_ne_zero (hp : p ≠ 0) (hm : m ≠ 0) (y : referenceLocus X D U) :
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val ≠ 0 := by
  let W := U ⊓ D.domain
  let z : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X W := referenceLocusIntersectionMap X D U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  let t : Γ(X.carrier, W)ˣ := referenceUnitOnIntersection X D U
  let q : Γ(X.carrier, W) := X.carrier.presheaf.map (homOfLE inf_le_left).op p
  let w : Γ(X.carrier, W)ˣ := Units.map
    (X.carrier.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom v
  have hfield : X.carrier.germToFunctionField W t =
      X.carrier.germToFunctionField W w * (X.carrier.germToFunctionField W q) ^ m := by
    change X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE inf_le_right).op (D.unit : Γ(X.carrier, D.domain))) =
      X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.carrier, U))) *
        (X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE inf_le_left).op p)) ^ m
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, D.represents]
    exact he
  have hpW : X.carrier.germToFunctionField W q ≠ 0 := by
    change X.carrier.germToFunctionField W (X.carrier.presheaf.map (homOfLE inf_le_left).op p) ≠ 0
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict]
    exact (map_ne_zero_iff _ (X.carrier.germToFunctionField_injective U)).mpr hp
  have h := HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.integer_power_parameter_nonzero (X.carrier.germToFunctionField W).hom
    (X.carrier.germToFunctionField_injective W) (HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation.sectionEvaluationHom (X := X) W z)
    t w q m hm hpW hfield (t.isUnit.map _).ne_zero (w.isUnit.map _).ne_zero
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (X.carrier.presheaf.map (homOfLE inf_le_left).op p) z ≠ 0 at h
  rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation.Constructions
