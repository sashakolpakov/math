import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionsLeftExact

/-! # Closed Support Intersection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedSupportIntersection

noncomputable section

section

/-! Imposing both closed support conditions gives their literal intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O C : Opens X)
variable (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X)

theorem sheafRestriction_sup_zero (U : Opens X) (s : F.obj.obj (op U))
    (hO : F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op s = 0)
    (hC : F.obj.map (homOfLE (inf_le_left : U ⊓ C ≤ U)).op s = 0) :
    F.obj.map (homOfLE (inf_le_left : U ⊓ (O ⊔ C) ≤ U)).op s = 0 := by
  apply F.eq_of_locally_eq₂
    (homOfLE (inf_le_inf_left U le_sup_left : U ⊓ O ≤ U ⊓ (O ⊔ C)))
    (homOfLE (inf_le_inf_left U le_sup_right : U ⊓ C ≤ U ⊓ (O ⊔ C)))
    (le_of_eq (inf_sup_left U O C))
  · rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    exact hO
  · rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    exact hC

def closedSupportIntersectionInclusion : CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ⟶ F :=
  CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F

theorem closedSupportIntersectionInclusion_zero :
    closedSupportIntersectionInclusion O C F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen (O ⊔ C) F = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change F.obj.map (homOfLE (inf_le_left : U.unop ⊓ (O ⊔ C) ≤ U.unop)).op
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.app U
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F)).hom.app U s)) = 0
  apply sheafRestriction_sup_zero O C F U.unop
  · have hn := ConcreteCategory.congr_hom
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.naturality
        (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op)
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F)).hom.app U s)
    change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.app (op (U.unop ⊓ O))
        ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F).obj.map (homOfLE (inf_le_left : U.unop ⊓ O ≤ U.unop)).op
          ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F)).hom.app U s)) = _ at hn
    rw [CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes, map_zero] at hn
    exact hn.symm
  · exact CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes C U.unop F _

def closedSupportIntersectionMap :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ⟶ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf (O ⊔ C) F :=
  kernel.lift (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen (O ⊔ C) F) (closedSupportIntersectionInclusion O C F)
    (closedSupportIntersectionInclusion_zero O C F)

@[reassoc (attr := simp)]
theorem closedSupportIntersectionMap_inclusion :
    closedSupportIntersectionMap O C F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (O ⊔ C) F =
      closedSupportIntersectionInclusion O C F := kernel.lift_ι _ _ _

theorem closedSupportIntersectionMap_surjective (U : Opens X) :
    Function.Surjective ((closedSupportIntersectionMap O C F).hom.app (op U)) := by
  intro s
  let q := (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (O ⊔ C) F).hom.app (op U) s
  have hz (D : Opens X) (hD : D ≤ O ⊔ C) :
      F.obj.map (homOfLE (inf_le_left : U ⊓ D ≤ U)).op q = 0 := by
    have h := congrArg
      (F.obj.map (homOfLE (inf_le_inf_left U hD : U ⊓ D ≤ U ⊓ (O ⊔ C))).op)
      (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes (O ⊔ C) U F s)
    rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp] at h
    exact h
  obtain ⟨t, ht⟩ := Supported.SectionsLeftExact.exists_supportedSection C U F q (hz C le_sup_right)
  have htO : (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F).obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op t = 0 := by
    apply CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective C (U ⊓ O) F
    rw [map_zero]
    have hn := ConcreteCategory.congr_hom
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.naturality
        (homOfLE (inf_le_left : U ⊓ O ≤ U)).op) t
    change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F).hom.app (op (U ⊓ O))
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F).obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op t) =
      F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op (Supported.SectionsLeftExact.supportedSectionsInclusion C U F t) at hn
    rw [ht] at hn
    exact hn.trans (hz O le_sup_left)
  obtain ⟨v, hv⟩ := Supported.SectionsLeftExact.exists_supportedSection O U (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) t htO
  refine ⟨v, ?_⟩
  apply CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective (O ⊔ C) U F
  have hn := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op U)) (closedSupportIntersectionMap_inclusion O C F)) v
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (O ⊔ C) F).hom.app (op U)
      ((closedSupportIntersectionMap O C F).hom.app (op U) v) =
    Supported.SectionsLeftExact.supportedSectionsInclusion C U F (Supported.SectionsLeftExact.supportedSectionsInclusion O U (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) v) at hn
  rw [hv, ht] at hn
  exact hn

def closedSupportIntersectionIso :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≅ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf (O ⊔ C) F := by
  have hm : Mono (closedSupportIntersectionMap O C F) := by
    have : Mono (closedSupportIntersectionMap O C F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (O ⊔ C) F) := by
      rw [closedSupportIntersectionMap_inclusion]
      change Mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F)
      infer_instance
    exact mono_of_mono (closedSupportIntersectionMap O C F) (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (O ⊔ C) F)
  have he : Epi (closedSupportIntersectionMap O C F).hom := by
    apply (NatTrans.epi_iff_epi_app _).mpr
    intro U
    exact (ModuleCat.epi_iff_surjective _).mpr (closedSupportIntersectionMap_surjective O C F U.unop)
  have : Epi (closedSupportIntersectionMap O C F) := by
    exact (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).epi_of_epi_map he
  have := isIso_of_mono_of_epi (closedSupportIntersectionMap O C F)
  exact asIso (closedSupportIntersectionMap O C F)

end

/-! The original nested support complexes and their inclusions identify with the literal intersection support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O C : Opens X)

theorem closedSupportIntersectionMap_naturality
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : F ⟶ G) :
    ClosedSupportFunctor.closedSupportSheafMap O (ClosedSupportFunctor.closedSupportSheafMap C f) ≫ closedSupportIntersectionMap O C G =
      closedSupportIntersectionMap O C F ≫ ClosedSupportFunctor.closedSupportSheafMap (O ⊔ C) f := by
  apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (O ⊔ C) G)).mp
  simp only [Category.assoc, closedSupportIntersectionMap_inclusion,
    ClosedSupportFunctor.closedSupportSheafMap_inclusion, closedSupportIntersectionMap_inclusion_assoc]
  unfold closedSupportIntersectionInclusion
  simp only [Category.assoc, ClosedSupportFunctor.closedSupportSheafMap_inclusion_assoc, ClosedSupportFunctor.closedSupportSheafMap_inclusion]

def closedSupportIntersectionFunctorIso :
    ClosedSupportFunctor.closedSupportSheafFunctor (R := ℚ) C ⋙ ClosedSupportFunctor.closedSupportSheafFunctor O ≅
      ClosedSupportFunctor.closedSupportSheafFunctor (O ⊔ C) :=
  NatIso.ofComponents (closedSupportIntersectionIso O C)
    (fun f => closedSupportIntersectionMap_naturality O C f)

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)

def supportedIntersectionComplexIso :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≅ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex (O ⊔ C) K :=
  ClosedSupportFunctor.supportedSheafComplexFunctorIso O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≪≫
    ((ClosedSupportFunctor.closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (ClosedSupportFunctor.supportedSheafComplexFunctorIso C K) ≪≫
    (NatIso.mapHomologicalComplex (closedSupportIntersectionFunctorIso O C) (ComplexShape.up ℕ)).app K ≪≫
    (ClosedSupportFunctor.supportedSheafComplexFunctorIso (O ⊔ C) K).symm

theorem supportedSheafComplexDegreeIso_inv_inclusion (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso C K n).inv ≫ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K).f n =
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C (K.X n) := by
  rw [← CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion C K n, Iso.inv_hom_id_assoc]

theorem supportedIntersectionComplexIso_inclusion :
    (supportedIntersectionComplexIso O C K).hom ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion (O ⊔ C) K =
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) n).hom ≫
      ClosedSupportFunctor.closedSupportSheafMap O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso C K n).hom ≫
      closedSupportIntersectionMap O C (K.X n) ≫ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso (O ⊔ C) K n).inv) ≫
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion (O ⊔ C) K).f n =
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K)).f n ≫
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K).f n
  simp only [Category.assoc, supportedSheafComplexDegreeIso_inv_inclusion,
    closedSupportIntersectionMap_inclusion]
  unfold closedSupportIntersectionInclusion
  simp only [ClosedSupportFunctor.closedSupportSheafMap_inclusion_assoc,
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion_assoc, CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedSupportIntersection
