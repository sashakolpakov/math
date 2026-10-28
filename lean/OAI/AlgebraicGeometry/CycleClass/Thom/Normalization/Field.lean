import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields

/-! # Field -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions

noncomputable section

/-! The finite normalization is Noetherian and preserves the actual
function field over the complex base, hence preserves dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include f in
theorem finiteNormalization_noetherian : AlgebraicGeometry.IsNoetherian (Normalization.Scheme.Constructions.normalization X) := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  let : IsLocallyNoetherian (Normalization.Scheme.Constructions.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalization.Scheme.Constructions.normalizationMap X ≫ f)
  let : CompactSpace (Normalization.Scheme.Constructions.normalization X) :=
    QuasiCompact.compactSpace_of_compactSpace (Normalization.Scheme.Constructions.normalizationMap X)
  exact ⟨⟩

def normalizationScalarFieldEquiv :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Normalization.Scheme.Constructions.normalizationMap X ≫ f)
    X.functionField ≃ₐ[ℂ] (Normalization.Scheme.Constructions.normalization X).functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Normalization.Scheme.Constructions.normalizationMap X ≫ f)
  exact AlgEquiv.ofBijective
    (ProperImage.FunctionFields.Constructions.Construction.genericFieldAlgHom (Normalization.Scheme.Constructions.normalizationMap X) (Fields.Constructions.normalizationMap_genericPoint X) f)
    (Fields.Constructions.normalizationFieldMap_bijective X)

omit [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f] in
theorem finiteNormalization_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Normalization.Scheme.Constructions.normalizationMap X ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Normalization.Scheme.Constructions.normalizationMap X ≫ f)
  exact congrArg Cardinal.toNat (normalizationScalarFieldEquiv X f).trdeg_eq.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions
