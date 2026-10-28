import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields

/-! # Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

noncomputable section

/-! The finite normalization preserves the actual function field. The
isomorphism is the generic-stalk pullback of the constructed normalization
morphism, with its compatibility with germs proved explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]

theorem normalizationMap_genericPoint :
    Normalization.Scheme.normalizationMap X (genericPoint (Normalization.Scheme.normalization X)) = genericPoint X := by
  apply IsGenericPoint.eq _ (genericPoint_spec X)
  have h := (genericPoint_spec (Normalization.Scheme.normalization X)).image (Normalization.Scheme.normalizationMap X).continuous
  simpa only [Set.image_univ, (Normalization.Scheme.normalizationMap X).denseRange.closure_range] using h

def normalizationFieldMap : X.functionField ⟶ (Normalization.Scheme.normalization X).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.Scheme.normalizationMap X) (normalizationMap_genericPoint X)

theorem normalizationFieldMap_finrank :
    letI := (normalizationFieldMap X).hom.toAlgebra
    Module.finrank X.functionField (Normalization.Scheme.normalization X).functionField = 1 :=
  (Support.Fields.genericFieldMap_finrank_eq_residueDegree
    (Normalization.Scheme.normalizationMap X) (normalizationMap_genericPoint X)).trans
      (Normalization.Scheme.normalizationMap_generic_residueDegree X)

theorem normalizationFieldMap_bijective : Function.Bijective (normalizationFieldMap X) := by
  let := (normalizationFieldMap X).hom.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (normalizationFieldMap_finrank X)

def normalizationFieldIso : X.functionField ≅ (Normalization.Scheme.normalization X).functionField :=
  (RingEquiv.ofBijective (normalizationFieldMap X).hom
    (normalizationFieldMap_bijective X)).toCommRingCatIso

theorem normalizationFieldIso_germ :
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫ (normalizationFieldIso X).hom =
      (Normalization.Scheme.normalizationMap X).appTop ≫
        (Normalization.Scheme.normalization X).presheaf.germ ⊤ (genericPoint (Normalization.Scheme.normalization X)) (by trivial) :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap_germ (Normalization.Scheme.normalizationMap X) (normalizationMap_genericPoint X)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields
