import OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule

/-! # Support Section Germ -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm.Constructions

noncomputable section

/-! Restricting a regular section to the actual reduced support commutes
with the actual support stalk map and its map to the function field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme)

theorem germ_eqToHom (U : X.Opens) (x y : X) (h : x = y) (hx : x ∈ U) (hy : y ∈ U) :
    X.presheaf.germ U x hx ≫ eqToHom (congrArg (fun z => X.presheaf.stalk z) h) =
      X.presheaf.germ U y hy := by
  subst y
  simp only [eqToHom_refl, Category.comp_id]

variable (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))
  (U : X.Opens) (hU : x ∈ U)

include hU in
theorem supportPreimage_mem_open : IntersectionGeometry.supportPreimage W x hx ∈ (Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U :=
  (congrArg (fun y : X => y ∈ U) (IntersectionGeometry.supportPreimage_spec W x hx)).mpr hU

theorem supportStalkMap_germ :
    X.presheaf.germ U x hU ≫ SupportStalkModule.Constructions.supportStalkMap X W x hx =
      (Geometric.GenericPoint.reducedSupportι W).app U ≫
        (Geometric.GenericPoint.reducedSupportScheme W).presheaf.germ ((Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U) (IntersectionGeometry.supportPreimage W x hx)
          (supportPreimage_mem_open X W x hx U hU) := by
  rw [SupportStalkModule.Constructions.supportStalkMap, ← Category.assoc]
  exact (congrArg (fun k => k ≫ (Geometric.GenericPoint.reducedSupportι W).stalkMap (IntersectionGeometry.supportPreimage W x hx))
    (germ_eqToHom X U x ((Geometric.GenericPoint.reducedSupportι W) (IntersectionGeometry.supportPreimage W x hx))
      (IntersectionGeometry.supportPreimage_spec W x hx).symm hU (supportPreimage_mem_open X W x hx U hU))).trans
    ((Geometric.GenericPoint.reducedSupportι W).germ_stalkMap U (IntersectionGeometry.supportPreimage W x hx) _)

variable [Nonempty ((Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U)]

theorem restrictedFunction_eq_supportStalk_germ (s : Γ(X, U)) :
    (Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ((Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U)
      ((Geometric.GenericPoint.reducedSupportι W).app U s) =
    algebraMap ((Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (IntersectionGeometry.supportPreimage W x hx))
      (Geometric.GenericPoint.reducedSupportScheme W).functionField (SupportStalkModule.Constructions.supportStalkMap X W x hx (X.presheaf.germ U x hU s)) := by
  have h := ConcreteCategory.congr_hom (supportStalkMap_germ X W x hx U hU) s
  rw [← (Geometric.GenericPoint.reducedSupportScheme W).algebraMap_germ_eq_germToFunctionField
    (supportPreimage_mem_open X W x hx U hU) ((Geometric.GenericPoint.reducedSupportι W).app U s)]
  exact congrArg (algebraMap ((Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (IntersectionGeometry.supportPreimage W x hx))
    (Geometric.GenericPoint.reducedSupportScheme W).functionField) h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm.Constructions
