import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionQuasiIso

/-! # Closed Support Functor -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedSupportFunctor

noncomputable section

/-! The original closed-support kernel is an additive functor on module sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] {X : TopCat.{0}} (O : Opens X)

def closedSupportSheafMap {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : F ⟶ G) :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F ⟶ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O G :=
  kernel.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F) (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O G) f
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.openRestrictionPushforwardFunctor O).map f)
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpenNatTrans O).naturality f).symm

@[reassoc (attr := simp)]
theorem closedSupportSheafMap_inclusion {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : F ⟶ G) :
    closedSupportSheafMap O f ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O G =
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F ≫ f :=
  kernel.lift_ι _ _ _

instance closedSupportSheafInclusion_mono (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F) :=
  inferInstanceAs (Mono (kernel.ι (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F)))

def closedSupportSheafFunctor :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X where
  obj F := CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F
  map f := closedSupportSheafMap O f
  map_id F := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F)).mp
    simp only [closedSupportSheafMap_inclusion, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O _)).mp
    simp only [Category.assoc, closedSupportSheafMap_inclusion, closedSupportSheafMap_inclusion_assoc]

instance closedSupportSheafFunctor_additive : (closedSupportSheafFunctor (R := R) O).Additive where
  map_add {F G} f g := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O G)).mp
    change closedSupportSheafMap O (f + g) ≫ _ =
      (closedSupportSheafMap O f + closedSupportSheafMap O g) ≫ _
    simp only [Preadditive.add_comp, closedSupportSheafMap_inclusion, Preadditive.comp_add]

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)

def supportedSheafComplexFunctorIso :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K ≅
      ((closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K) ?_
  intro i j hij
  apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X j))).mp
  change (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K i).hom ≫
      closedSupportSheafMap O (K.d i j) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X j) =
    ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K).d i j ≫
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K j).hom) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X j)
  simp only [Category.assoc, closedSupportSheafMap_inclusion,
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion_assoc, CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion]
  exact (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K).comm i j

theorem supportedSheafComplexFunctorIso_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ} (f : K ⟶ L) :
    Supported.SectionQuasiIso.supportedSheafComplexMap O f ≫ (supportedSheafComplexFunctorIso O L).hom =
      (supportedSheafComplexFunctorIso O K).hom ≫
        ((closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (L.X n))).mp
  change ((Supported.SectionQuasiIso.supportedSheafComplexMap O f).f n ≫ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O L n).hom) ≫
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (L.X n) =
    ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K n).hom ≫ closedSupportSheafMap O (f.f n)) ≫
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (L.X n)
  simp only [Category.assoc, closedSupportSheafMap_inclusion,
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion_assoc, CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion]
  exact congrArg (fun g => g.f n) (Supported.SectionQuasiIso.supportedSheafComplexMap_inclusion O f)

def supportedSheafComplexMapHomotopy
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}
    {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (Supported.SectionQuasiIso.supportedSheafComplexMap O f) (Supported.SectionQuasiIso.supportedSheafComplexMap O g) := by
  have hu (u : K ⟶ L) :
      ((supportedSheafComplexFunctorIso O K).hom ≫
        ((closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map u) ≫
          (supportedSheafComplexFunctorIso O L).inv = Supported.SectionQuasiIso.supportedSheafComplexMap O u := by
    rw [← supportedSheafComplexFunctorIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := (((closedSupportSheafFunctor O).mapHomotopy h).compLeft
    (supportedSheafComplexFunctorIso O K).hom).compRight
      (supportedSheafComplexFunctorIso O L).inv
  rw [hu f, hu g] at hh
  exact hh

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedSupportFunctor
