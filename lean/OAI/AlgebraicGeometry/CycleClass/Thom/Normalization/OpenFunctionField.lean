import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary

/-! # Open Function Field -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions

noncomputable section

/-! Every rational function on an actual normalization open comes from
the original parent support through the constructed birational field
isomorphisms; the equality is proved, not supplied as divisor data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : IsIntegral (AmbientMap.Constructions.fullNormalizationOver V W).left :=
  inferInstanceAs (IsIntegral (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W)))
local instance : IsIntegral (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) : Scheme) :=
  AmbientTopology.Constructions.smoothNormalization_integral V W
local instance : Nonempty ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) :=
  inferInstanceAs (Nonempty (((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W) : Scheme))

def normalizedFieldIso : (Geometric.GenericPoint.reducedSupportScheme W).functionField ≅ (AmbientMap.Constructions.smoothNormalizationOver V W).left.functionField :=
  Fields.Constructions.normalizationFieldIso (Geometric.GenericPoint.reducedSupportScheme W) ≪≫
    RationalOrderTransport.Constructions.openFunctionFieldIso ((AmbientMap.Constructions.normalizationToAmbient V W).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V W).ι

theorem normalizedFunction_eq_iso (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    PrincipalBoundary.Constructions.normalizedFunction V W g = (normalizedFieldIso V W).hom g := rfl

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]

def sourceFieldIso : (Geometric.GenericPoint.reducedSupportScheme W).functionField ≅ X.left.functionField :=
  normalizedFieldIso V W ≪≫ RationalOrderTransport.Constructions.openFunctionFieldIso a.left

def originalFunction (r : X.left.functionField) : (Geometric.GenericPoint.reducedSupportScheme W).functionField :=
  (sourceFieldIso V W a).inv r

theorem originalFunction_pullback (r : X.left.functionField) :
    RationalOrderTransport.Constructions.openFunctionFieldMap a.left (PrincipalBoundary.Constructions.normalizedFunction V W (originalFunction V W a r)) = r :=
  (sourceFieldIso V W a).inv_hom_id_apply r

theorem originalFunction_ne_zero (r : X.left.functionField) (hr : r ≠ 0) :
    originalFunction V W a r ≠ 0 := by
  intro hz
  apply hr
  have h := originalFunction_pullback V W a r
  rw [hz, PrincipalBoundary.Constructions.normalizedFunction, map_zero, map_zero, map_zero] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions
