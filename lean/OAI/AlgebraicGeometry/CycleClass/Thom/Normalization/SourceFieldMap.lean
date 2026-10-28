import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField
import OAI.AlgebraicGeometry.CycleClass.Thom.GenericFieldComposition

/-! # Source Field Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SourceFieldMap.Constructions

noncomputable section

/-! The constructed source field isomorphism is the actual generic-stalk
map to the original support. Its inverse sends pulled-back regular germs
to those same original germs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GenericFieldComposition.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : IsIntegral (AmbientMap.Constructions.fullNormalizationOver V W).left :=
  inferInstanceAs (IsIntegral (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W)))
local instance : IsIntegral (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) : Scheme) :=
  AmbientTopology.Constructions.smoothNormalization_integral V W

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]

def sourceToSupport : X.left ⟶ Geometric.GenericPoint.reducedSupportScheme W :=
  a.left ≫ ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι ≫ Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)

theorem sourceToSupport_genericPoint :
    sourceToSupport V W a (genericPoint X.left) = genericPoint (Geometric.GenericPoint.reducedSupportScheme W) := by
  have ha := genericPoint_eq_of_isOpenImmersion a.left
  have hu := genericPoint_eq_of_isOpenImmersion ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι
  exact (congrArg (fun y => Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)
    (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι y)) ha).trans
    ((congrArg (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)) hu).trans
      (Fields.Constructions.normalizationMap_genericPoint (Geometric.GenericPoint.reducedSupportScheme W)))

theorem sourceFieldIso_hom_eq_genericFieldMap :
    (OpenFunctionField.Constructions.sourceFieldIso V W a).hom = RationalOrderTransport.Constructions.genericFieldMap (sourceToSupport V W a) (sourceToSupport_genericPoint V W a) := by
  let u : (AmbientMap.Constructions.smoothNormalizationOver V W).left ⟶ Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W) :=
    ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι
  let n := Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W)
  have hu := genericPoint_eq_of_isOpenImmersion u
  have hn := Fields.Constructions.normalizationMap_genericPoint (Geometric.GenericPoint.reducedSupportScheme W)
  have ha := genericPoint_eq_of_isOpenImmersion a.left
  have h₁ := GenericFieldComposition.Constructions.genericFieldMap_comp u n hu hn
  have h₂ := GenericFieldComposition.Constructions.genericFieldMap_comp a.left (u ≫ n) ha ((congrArg n hu).trans hn)
  exact (congrArg (fun k => k ≫ RationalOrderTransport.Constructions.genericFieldMap a.left ha) h₁.symm).trans h₂.symm

omit [IsIntegral X.left] [IsOpenImmersion a.left] in

theorem sourceToSupport_ambient : sourceToSupport V W a ≫ Geometric.GenericPoint.reducedSupportι W =
    (a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W).left := by
  rw [sourceToSupport, Over.comp_left, PrincipalBoundary.Constructions.fullAmbientMap_left]
  simp only [Category.assoc]

local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

theorem originalFunction_germ_appLE (U : (Geometric.GenericPoint.reducedSupportScheme W).Opens) [Nonempty U]
    (hU : (⊤ : X.left.Opens) ≤ sourceToSupport V W a ⁻¹ᵁ U) (s : Γ(Geometric.GenericPoint.reducedSupportScheme W, U)) :
    OpenFunctionField.Constructions.originalFunction V W a (X.left.germToFunctionField ⊤ ((sourceToSupport V W a).appLE U ⊤ hU s)) =
      (Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField U s := by
  apply (OpenFunctionField.Constructions.sourceFieldIso V W a).hom.hom.injective
  change (OpenFunctionField.Constructions.sourceFieldIso V W a).hom ((OpenFunctionField.Constructions.sourceFieldIso V W a).inv _) = _
  rw [Iso.inv_hom_id_apply, sourceFieldIso_hom_eq_genericFieldMap]
  exact (ConcreteCategory.congr_hom
    (GenericFieldComposition.Constructions.genericFieldMap_germ_appLE (sourceToSupport V W a) (sourceToSupport_genericPoint V W a) U ⊤ hU) s).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SourceFieldMap.Constructions
