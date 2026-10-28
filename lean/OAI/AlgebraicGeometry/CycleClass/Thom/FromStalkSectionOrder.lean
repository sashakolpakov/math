import OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalField
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder

/-! # From Stalk Section Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkSectionOrder.Constructions

noncomputable section

/-! The actual section germ in a stalk gives the same rational function
and the same scheme orders as the original regular section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GenericFieldComposition.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme) [IsIntegral X] (x : X) (B : X.Opens) [Nonempty B] (hxB : x ∈ B) (s : Γ(X, B))

local instance : Nonempty (⊤ : (Spec (X.presheaf.stalk x)).Opens) :=
  ⟨⟨genericPoint (Spec (X.presheaf.stalk x)), Opens.mem_top _⟩⟩

theorem stalkFieldMap_section :
    FromStalkOrder.Constructions.stalkFieldMap X x (X.germToFunctionField B s) =
      Affine.PrincipalSchemeOrder.Constructions.affineFunction (X.presheaf.stalk x) (X.presheaf.germ B x hxB s) := by
  have h := GenericFieldComposition.Constructions.genericFieldMap_germ_appLE (X.fromSpecStalk x) (SupportStalkModule.Constructions.genericPoint_image X x)
    B ⊤ (le_of_eq (NormalizedLocalField.Constructions.Normalization.fromSpecStalk_preimage X B ⟨x, hxB⟩).symm)
  rw [NormalizedLocalField.Constructions.Normalization.fromSpecStalk_appLE X B ⟨x, hxB⟩] at h
  exact ConcreteCategory.congr_hom h s

variable [IsLocallyNoetherian X]

theorem ord_stalkSection (y : Spec (X.presheaf.stalk x)) :
    (Spec (X.presheaf.stalk x)).ord (Affine.PrincipalSchemeOrder.Constructions.affineFunction (X.presheaf.stalk x) (X.presheaf.germ B x hxB s)) y =
      X.ord (X.germToFunctionField B s) (X.fromSpecStalk x y) :=
  (congrArg (fun g => (Spec (X.presheaf.stalk x)).ord g y) (stalkFieldMap_section X x B hxB s)).symm.trans
    (FromStalkOrder.Constructions.ord_fromSpecStalk X x (X.germToFunctionField B s) y)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkSectionOrder.Constructions
