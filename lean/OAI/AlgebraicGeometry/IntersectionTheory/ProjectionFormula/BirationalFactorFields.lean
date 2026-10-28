import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactor

/-! # Birational Factor Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactorFields

noncomputable section

/-! Function-field and norm compatibility of the constructed proper
birational factor through the finite intermediate normalization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

theorem intermediateMap_genericPoint :
    BirationalFactor.intermediateMap f hη (genericPoint (BirationalFactor.intermediate f hη)) = genericPoint Y := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  exact Relative.NormalizationFields.relativeNormalizationMap_genericPoint Y X.functionField

theorem factorFieldMap_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη) =
        Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη ≫ Normalization.Fields.normalizationFieldMap X := by
  rw [Normalization.Fields.normalizationFieldMap, ← Generic.Fields.genericFieldMap_comp,
    ← Generic.Fields.genericFieldMap_comp]
  exact Generic.Fields.genericFieldMap_congr (BirationalFactor.birationalFactor_comp f hη) _ _

variable (hfinite : letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  Module.Finite Y.functionField X.functionField)

def factorFunctionFieldIso : X.functionField ≅ (BirationalFactor.intermediate f hη).functionField := by
  let := BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  exact Normalization.Fields.normalizationFieldIso X ≪≫
    (asIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))).symm

theorem factorFunctionFieldIso_pullback (g : X.functionField) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη)
      ((factorFunctionFieldIso f hη hfinite).hom g) = (Normalization.Fields.normalizationFieldIso X).hom g := by
  let := BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  change (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))
    (inv (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))
      ((Normalization.Fields.normalizationFieldIso X).hom g)) = _
  change (inv (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη)) ≫
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη))
      ((Normalization.Fields.normalizationFieldIso X).hom g) = _
  rw [IsIso.inv_hom_id]
  rfl

theorem factorFunctionFieldIso_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη ≫ (factorFunctionFieldIso f hη hfinite).hom =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη) := by
  let := BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  apply (cancel_mono (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.birationalFactor f hη)
    (BirationalFactor.birationalFactor_genericPoint f hη))).mp
  rw [factorFieldMap_square]
  ext g
  exact factorFunctionFieldIso_pullback f hη hfinite (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g)

theorem factorFunctionFieldIso_norm (g : X.functionField) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη)).hom.toAlgebra
    Algebra.norm Y.functionField ((factorFunctionFieldIso f hη hfinite).hom g) =
      Algebra.norm Y.functionField g := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (intermediateMap_genericPoint f hη)).hom.toAlgebra
  exact (Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl Y.functionField)
    (factorFunctionFieldIso f hη hfinite).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (factorFunctionFieldIso_square f hη hfinite).symm) g).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactorFields
