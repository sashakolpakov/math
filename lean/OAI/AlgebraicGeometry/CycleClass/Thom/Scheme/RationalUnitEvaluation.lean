import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation
import OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding

/-! # Rational Unit Evaluation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalUnitEvaluation.Constructions

noncomputable section

/-! Evaluate an actual rational-function local power identity on the common
unit domain, including negative exponents and its forced nonzero parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal OAI.AlgebraicGeometry.CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

def referenceLocus (U : X.left.Opens) : Set (SectionEvaluation.Constructions.analyticOpen X U) :=
  {y | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ D.domain}

def referenceLocusIntersectionMap (U : X.left.Opens) :
    C(referenceLocus X D U, SectionEvaluation.Constructions.analyticOpen X (U ⊓ D.domain)) :=
  ⟨fun y => ⟨y.val.val, y.val.property, y.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def referenceUnitOnIntersection (U : X.left.Opens) : Γ(X.left, U ⊓ D.domain)ˣ :=
  Units.map (X.left.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom D.unit

def referenceEquation (U : X.left.Opens) : C(referenceLocus X D U, ℂ) :=
  (SectionEvaluation.Constructions.sectionEvaluationOn X (U ⊓ D.domain) (referenceUnitOnIntersection X D U)).comp
    (referenceLocusIntersectionMap X D U)

theorem referenceEquation_ne_zero (U : X.left.Opens) (y : referenceLocus X D U) :
    referenceEquation X D U y ≠ 0 :=
  SectionEvaluation.Constructions.sectionEvaluationOn_unit_ne_zero X (U ⊓ D.domain) (referenceUnitOnIntersection X D U) _

variable (U : X.left.Opens) [Nonempty U]
  (p : Γ(X.left, U)) (v : Γ(X.left, U)ˣ) (m : ℤ)
  (he : g = X.left.germToFunctionField U v * (X.left.germToFunctionField U p) ^ m)

include he

theorem referenceEquation_power (y : referenceLocus X D U)
    (hp : SectionEvaluation.Constructions.sectionEvaluationOn X U p y.val ≠ 0) :
    referenceEquation X D U y = SectionEvaluation.Constructions.sectionEvaluationOn X U (v : Γ(X.left, U)) y.val *
      (SectionEvaluation.Constructions.sectionEvaluationOn X U p y.val) ^ m := by
  let W := U ⊓ D.domain
  let z : SectionEvaluation.Constructions.analyticOpen X W := referenceLocusIntersectionMap X D U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  let t : Γ(X.left, W)ˣ := referenceUnitOnIntersection X D U
  let q : Γ(X.left, W) := X.left.presheaf.map (homOfLE inf_le_left).op p
  let w : Γ(X.left, W) := X.left.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.left, U))
  have hfield : X.left.germToFunctionField W t =
      X.left.germToFunctionField W w * (X.left.germToFunctionField W q) ^ m := by
    change X.left.germToFunctionField W (X.left.presheaf.map (homOfLE inf_le_right).op (D.unit : Γ(X.left, D.domain))) =
      X.left.germToFunctionField W (X.left.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.left, U))) *
        (X.left.germToFunctionField W (X.left.presheaf.map (homOfLE inf_le_left).op p)) ^ m
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, D.represents]
    exact he
  have hp' : SectionEvaluation.Constructions.sectionEvaluationHom X W z q ≠ 0 := by
    change SectionEvaluation.Constructions.sectionEvaluationOn X W (X.left.presheaf.map (homOfLE inf_le_left).op p) z ≠ 0
    rw [SectionEvaluation.Constructions.sectionEvaluationOn_restrict]
    exact hp
  have h := HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.evaluate_integer_power_relation (X.left.germToFunctionField W).hom
    (X.left.germToFunctionField_injective W) (SectionEvaluation.Constructions.sectionEvaluationHom X W z)
    t w q m hfield hp'
  change referenceEquation X D U y =
    SectionEvaluation.Constructions.sectionEvaluationOn X W (X.left.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.left, U))) z *
      (SectionEvaluation.Constructions.sectionEvaluationOn X W (X.left.presheaf.map (homOfLE inf_le_left).op p) z) ^ m at h
  rw [SectionEvaluation.Constructions.sectionEvaluationOn_restrict, SectionEvaluation.Constructions.sectionEvaluationOn_restrict] at h
  exact h

theorem referenceParameter_ne_zero (hp : p ≠ 0) (hm : m ≠ 0) (y : referenceLocus X D U) :
    SectionEvaluation.Constructions.sectionEvaluationOn X U p y.val ≠ 0 := by
  let W := U ⊓ D.domain
  let z : SectionEvaluation.Constructions.analyticOpen X W := referenceLocusIntersectionMap X D U y
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z.val, z.property⟩⟩
  let t : Γ(X.left, W)ˣ := referenceUnitOnIntersection X D U
  let q : Γ(X.left, W) := X.left.presheaf.map (homOfLE inf_le_left).op p
  let w : Γ(X.left, W)ˣ := Units.map
    (X.left.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom v
  have hfield : X.left.germToFunctionField W t =
      X.left.germToFunctionField W w * (X.left.germToFunctionField W q) ^ m := by
    change X.left.germToFunctionField W (X.left.presheaf.map (homOfLE inf_le_right).op (D.unit : Γ(X.left, D.domain))) =
      X.left.germToFunctionField W (X.left.presheaf.map (homOfLE inf_le_left).op (v : Γ(X.left, U))) *
        (X.left.germToFunctionField W (X.left.presheaf.map (homOfLE inf_le_left).op p)) ^ m
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict, D.represents]
    exact he
  have hpW : X.left.germToFunctionField W q ≠ 0 := by
    change X.left.germToFunctionField W (X.left.presheaf.map (homOfLE inf_le_left).op p) ≠ 0
    rw [RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict]
    exact (map_ne_zero_iff _ (X.left.germToFunctionField_injective U)).mpr hp
  have h := HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.integer_power_parameter_nonzero (X.left.germToFunctionField W).hom
    (X.left.germToFunctionField_injective W) (SectionEvaluation.Constructions.sectionEvaluationHom X W z)
    t w q m hm hpW hfield (t.isUnit.map _).ne_zero (w.isUnit.map _).ne_zero
  change SectionEvaluation.Constructions.sectionEvaluationOn X W (X.left.presheaf.map (homOfLE inf_le_left).op p) z ≠ 0 at h
  rw [SectionEvaluation.Constructions.sectionEvaluationOn_restrict] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalUnitEvaluation.Constructions
