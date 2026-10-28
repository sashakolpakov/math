import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs

/-! # Intersect Support Sheaf -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportSheaf.Constructions

noncomputable section

/-! Two genuine closed-support conditions are exactly support in their intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}
variable (C O : Opens X) {G F : TopCat.Sheaf (ModuleCat.{0} R) X}

theorem sheafMorphism_restrict_sup_zero (f : G ⟶ F)
    (hC : f ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen C F = 0)
    (hO : f ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F = 0) :
    f ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen (C ⊔ O) F = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U x
  let V := U.unop
  change F.obj.map (homOfLE (inf_le_left : V ⊓ (C ⊔ O) ≤ V)).op (f.hom.app U x) = 0
  apply F.eq_of_locally_eq₂
    (homOfLE (inf_le_inf_left V le_sup_left : V ⊓ C ≤ V ⊓ (C ⊔ O)))
    (homOfLE (inf_le_inf_left V le_sup_right : V ⊓ O ≤ V ⊓ (C ⊔ O)))
    (le_of_eq (inf_sup_left V C O))
  · rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    exact ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U) hC) x
  · rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    exact ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U) hO) x

theorem sheafMorphism_restrict_zero_of_le {C D : Opens X} (h : C ≤ D) (f : G ⟶ F)
    (hf : f ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen D F = 0) : f ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen C F = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U x
  have he := ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U) hf) x
  change F.obj.map (homOfLE (inf_le_left : U.unop ⊓ D ≤ U.unop)).op (f.hom.app U x) = 0 at he
  have he' := congrArg (F.obj.map (homOfLE (inf_le_inf_left U.unop h)).op) he
  rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp] at he'
  exact he'

variable (F)

def intersectSupportInclusion : CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ⟶ F :=
  CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F

instance intersectSupportInclusion_mono : Mono (intersectSupportInclusion C O F) :=
  inferInstanceAs (Mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≫
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F))

theorem intersectSupportInclusion_restrict_left :
    intersectSupportInclusion C O F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen C F = 0 := by
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≫
    kernel.ι (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen C F)) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen C F = 0
  rw [Category.assoc, kernel.condition, comp_zero]

theorem intersectSupportInclusion_restrict_right :
    intersectSupportInclusion C O F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F = 0 := by
  have hn : CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F =
      CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≫
        (CycleClass.Geometric.SheafClosedSupport.Cohomology.openRestrictionPushforwardFunctor O).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F) :=
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpenNatTrans O).naturality (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F)
  unfold intersectSupportInclusion
  rw [Category.assoc, hn, ← Category.assoc]
  change (kernel.ι (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F)) ≫
    CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F)) ≫ _ = 0
  rw [kernel.condition, zero_comp]

def intersectSupportToUnion :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ⟶ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf (C ⊔ O) F :=
  kernel.lift _ (intersectSupportInclusion C O F)
    (sheafMorphism_restrict_sup_zero C O _ (intersectSupportInclusion_restrict_left C O F)
      (intersectSupportInclusion_restrict_right C O F))

@[reassoc]
theorem intersectSupportToUnion_inclusion :
    intersectSupportToUnion C O F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) F =
      intersectSupportInclusion C O F := kernel.lift_ι _ _ _

def unionSupportToLeft : CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf (C ⊔ O) F ⟶ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F :=
  kernel.lift _ (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) F)
    (sheafMorphism_restrict_zero_of_le le_sup_left _ (kernel.condition _))

@[reassoc]
theorem unionSupportToLeft_inclusion :
    unionSupportToLeft C O F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F =
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) F := kernel.lift_ι _ _ _

theorem unionSupportToLeft_restrict_zero :
    unionSupportToLeft C O F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U x
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F).obj.map
    (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op
      ((unionSupportToLeft C O F).hom.app U x) = 0
  apply CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective C (U.unop ⊓ O) F
  rw [map_zero]
  have hn := ConcreteCategory.congr_hom
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.naturality
      (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op)
    ((unionSupportToLeft C O F).hom.app U x)
  change ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.app (op (U.unop ⊓ O)))
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F).obj.map (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op
        ((unionSupportToLeft C O F).hom.app U x)) = _ at hn
  rw [hn]
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun q => q.hom.app U) (unionSupportToLeft_inclusion C O F)) x
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.app U ((unionSupportToLeft C O F).hom.app U x) = _ at hi
  change F.obj.map (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.app U ((unionSupportToLeft C O F).hom.app U x)) = 0
  rw [hi]
  exact ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U)
    (sheafMorphism_restrict_zero_of_le le_sup_right (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) F)
      (kernel.condition _))) x

def unionSupportToIntersect :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf (C ⊔ O) F ⟶ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) :=
  kernel.lift _ (unionSupportToLeft C O F) (unionSupportToLeft_restrict_zero C O F)

@[reassoc]
theorem unionSupportToIntersect_inclusion :
    unionSupportToIntersect C O F ≫ intersectSupportInclusion C O F =
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) F := by
  unfold intersectSupportInclusion
  rw [← Category.assoc]
  change (kernel.lift _ _ _ ≫ kernel.ι _) ≫ _ = _
  rw [kernel.lift_ι, unionSupportToLeft_inclusion]

def intersectSupportSheafIso :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≅ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf (C ⊔ O) F where
  hom := intersectSupportToUnion C O F
  inv := unionSupportToIntersect C O F
  hom_inv_id := by
    apply (cancel_mono (intersectSupportInclusion C O F)).mp
    rw [Category.assoc, unionSupportToIntersect_inclusion, intersectSupportToUnion_inclusion,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) F)).mp
    rw [Category.assoc, intersectSupportToUnion_inclusion, unionSupportToIntersect_inclusion,
      Category.id_comp]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportSheaf.Constructions
