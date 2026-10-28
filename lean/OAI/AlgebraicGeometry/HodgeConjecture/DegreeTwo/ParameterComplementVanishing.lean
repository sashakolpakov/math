import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding
import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations

/-! # Parameter Complement Vanishing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterComplementVanishing.Constructions

noncomputable section

/-!
# DegreeTwo: the actual Chern lift vanishes away from its local parameter

Where the regular parameter is nonzero, its winding extends as a unit
on the whole open set. Exactness therefore kills the actual relative
class, even if the reference complement has additional components.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations.AlgebraicLineBundle

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation

theorem rationalSectionChern_restrict_zero_of_parameter_nonzero
    {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]
    (i : X.carrier) (U : X.carrier.Opens) [Nonempty U] (hi : U ≤ L.trivializingOpen i)
    (p : Γ(X.carrier, U)) (hp : p ≠ 0) (v : Γ(X.carrier, U)ˣ)
    (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : X.carrier.functionField) =
      X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m)
    (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hWU : W ≤ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)
    (hWp : ∀ y : W, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p ⟨y.val, hWU y.property⟩ ≠ 0) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) W 2
      L.rationalSectionChernRelativeClass = 0 := by
  let Q := ModuleCat.of ℚ ℚ
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let A := L.analyticReferenceLocus W
  let j : TopCat.of W ⟶ TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :=
    TopCat.ofHom ⟨fun y => ⟨y.val, hWU y.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hj : Set.MapsTo j A (L.referenceLocus U) := fun _ hy => hy
  let s : C(W, ℂ) := (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p).comp j.hom
  have hs : ∀ y, s y ≠ 0 := hWp
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set T)) hj
    (A := A) (B := L.referenceLocus U)
    (C := (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T)) (fun _ hy => hy) 2
  have hv := (ConcreteCategory.congr_hom hc L.rationalSectionChernRelativeClass).symm
  change CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q T
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) W 2 L.rationalSectionChernRelativeClass =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q T
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
        L.rationalSectionChernRelativeClass) at hv
  rw [L.rationalSectionChernRelativeClass_algebraic i U hi,
    DivisorWinding.Constructions.DivisorEvaluation.rationalSectionLocalSupportedClass_power L i U hi p hp v m hm he, map_zsmul] at hv
  have hn := DivisorClass.Chern.Supported.Winding.supportedWindingClass_pullback (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (L.referenceLocus U)
    j A hj (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter L U p) (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he)
  have hz : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
      (DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (L.referenceLocus U)
        (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter L U p) (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he)) = 0 :=
    hn.trans (DivisorClass.Chern.Supported.Winding.supportedWindingClass_extending_unit (TopCat.of W) A s hs)
  exact hv.trans (by rw [hz, smul_zero])

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterComplementVanishing.Constructions
