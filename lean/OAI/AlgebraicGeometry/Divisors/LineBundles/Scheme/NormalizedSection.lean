import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrincipalCoefficients

/-! # Normalized Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedSection.BundleCycles

noncomputable section

/-! Normalizing and then restricting a global regular section gives exactly its actual germ on the smooth normalization open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (W : IrreducibleCloseds X.left)

local notation "S" => OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint.reducedSupportScheme W
local notation "U" => OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizedOpen X W

local instance normalizedSectionSupportTopNonempty : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩
local instance normalizedSectionFullTopNonempty : Nonempty (⊤ : (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)).Opens) :=
  ⟨⟨genericPoint (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)), Opens.mem_top _⟩⟩
local instance normalizedSectionOpenIntegral : IsIntegral ((U) : Scheme) := SchemeNormalization.Topology.BundleCycles.schemeSmoothNormalization_integral X W
local instance normalizedSectionOpenTopNonempty : Nonempty (⊤ : ((U) : Scheme).Opens) :=
  ⟨⟨genericPoint ((U) : Scheme), Opens.mem_top _⟩⟩

theorem schemeNormalizedFunction_supportSection (s : Γ(S, ⊤)) :
    NormalizedFunction.BundleCycles.schemeNormalizedFunction X W ((S).germToFunctionField ⊤ s) =
    (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤
      (((U).ι ≫ CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S).appTop s) := by
  have hn := ConcreteCategory.congr_hom (CycleClass.Thom.Normalization.Fields.Constructions.normalizationFieldIso_germ S) s
  change (CycleClass.Thom.Normalization.Fields.Constructions.normalizationFieldIso S).hom ((S).germToFunctionField ⊤ s) =
    (CycleClass.Thom.Normalization.Scheme.Constructions.normalization S).germToFunctionField ⊤ ((CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S).appTop s) at hn
  change RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (U).ι ((CycleClass.Thom.Normalization.Fields.Constructions.normalizationFieldIso S).hom ((S).germToFunctionField ⊤ s)) = _
  rw [hn]
  have hh := FiniteAffine.PrincipalCoefficients.BundleCycles.openFunctionFieldMap_globalSection (U).ι ((CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S).appTop s)
  have he := congrArg (fun f : Γ(S, ⊤) ⟶ Γ(((U) : Scheme), ⊤) => f s)
    (Scheme.Hom.comp_appTop (U).ι (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S))
  exact hh.trans (congrArg (((U) : Scheme).germToFunctionField ⊤) he.symm)

theorem schemeNormalizedFunction_ambientSection (s : Γ(X.left, ⊤)) :
    NormalizedFunction.BundleCycles.schemeNormalizedFunction X W ((S).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)) =
    (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤
      ((NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X W).left.appTop s) := by
  rw [schemeNormalizedFunction_supportSection]
  have hh := congrArg (fun f : (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left ⟶ X.left => f.appTop s)
    (NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap_left X W)
  have he : (((U).ι ≫ CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop =
      (NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X W).left.appTop :=
    congrArg Scheme.Hom.appTop ((Category.assoc _ _ _).trans (NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap_left X W).symm)
  have hsec := congrArg (fun f : Γ(X.left, ⊤) ⟶ Γ(((U) : Scheme), ⊤) => f s)
    ((Scheme.Hom.comp_appTop ((U).ι ≫ CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S) (CycleClass.Geometric.GenericPoint.reducedSupportι W)).symm.trans he)
  exact congrArg ((SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤) hsec

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedSection.BundleCycles
