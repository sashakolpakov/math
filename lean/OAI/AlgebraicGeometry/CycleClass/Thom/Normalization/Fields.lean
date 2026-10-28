import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.ResidueDegree

/-! # Fields -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions

noncomputable section

/-! The finite normalization preserves the actual function field. The
isomorphism is the generic-stalk pullback of the constructed normalization
morphism, with its compatibility with germs proved explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions

universe u

variable (X : Scheme.{u}) [IsIntegral X]

theorem normalizationMap_genericPoint :
    Normalization.Scheme.Constructions.normalizationMap X (genericPoint (Normalization.Scheme.Constructions.normalization X)) = genericPoint X := by
  apply IsGenericPoint.eq _ (genericPoint_spec X)
  have h := (genericPoint_spec (Normalization.Scheme.Constructions.normalization X)).image (Normalization.Scheme.Constructions.normalizationMap X).continuous
  simpa only [Set.image_univ, (Normalization.Scheme.Constructions.normalizationMap X).denseRange.closure_range] using h

def normalizationFieldMap : X.functionField ⟶ (Normalization.Scheme.Constructions.normalization X).functionField :=
  ProperImage.FunctionFields.Constructions.Construction.genericFieldMap (Normalization.Scheme.Constructions.normalizationMap X) (normalizationMap_genericPoint X)

theorem normalizationFieldMap_finrank :
    letI := (normalizationFieldMap X).hom.toAlgebra
    Module.finrank X.functionField (Normalization.Scheme.Constructions.normalization X).functionField = 1 :=
  (ProperImage.ResidueDegree.Constructions.Construction.genericFieldMap_finrank_eq_residueDegree
    (Normalization.Scheme.Constructions.normalizationMap X) (normalizationMap_genericPoint X)).trans
      (Normalization.Scheme.Constructions.normalizationMap_generic_residueDegree X)

theorem normalizationFieldMap_bijective : Function.Bijective (normalizationFieldMap X) := by
  let := (normalizationFieldMap X).hom.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (normalizationFieldMap_finrank X)

def normalizationFieldIso : X.functionField ≅ (Normalization.Scheme.Constructions.normalization X).functionField :=
  (RingEquiv.ofBijective (normalizationFieldMap X).hom
    (normalizationFieldMap_bijective X)).toCommRingCatIso

theorem normalizationFieldIso_germ :
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫ (normalizationFieldIso X).hom =
      (Normalization.Scheme.Constructions.normalizationMap X).appTop ≫
        (Normalization.Scheme.Constructions.normalization X).presheaf.germ ⊤ (genericPoint (Normalization.Scheme.Constructions.normalization X)) (by trivial) :=
  ProperImage.FunctionFields.Constructions.Construction.genericFieldMap_germ (Normalization.Scheme.Constructions.normalizationMap X) (normalizationMap_genericPoint X)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions
