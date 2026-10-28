import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ExtResolutionCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.HomComplexCycleCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendedCycleCoordinates

/-! # Resolution Injective -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ResolutionInjective

noncomputable section

section

/-! Explicit cochain coordinates for the unchanged native injective-resolution comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  (R : InjectiveResolution F)

local instance nativeResolutionCochains_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

def nativeResolutionSectionsIso :
    ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
      (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)).HomComplex R.cochainComplex ≅
        (FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extend ComplexShape.embeddingUpNat :=
  HomComplexSections.nativeHomComplexSectionsIso R.cochainComplex ≪≫
    ResolutionExtensionSections.resolutionMapExtendIso (G := SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) R.cocomplex

theorem nativeResolutionSectionsIso_fromSingle (k : ℕ)
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ R.cocomplex.X k) :
    (nativeResolutionSectionsIso R).hom.f (k : ℤ)
      (Cochain.fromSingleMk (f ≫ (R.cochainComplexXIso k k rfl).inv) (zero_add _)) =
        ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extendXIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)).inv
            (SectionCoordinates.nativeSheafHomGlobalEquiv (R.cocomplex.X k) f) := by
  change (ResolutionExtensionSections.resolutionMapExtendXIso (G := SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) R.cocomplex (k : ℤ)).hom
    ((HomComplexSections.nativeHomComplexSectionsIso R.cochainComplex).hom.f (k : ℤ)
      (Cochain.fromSingleMk (f ≫ (R.cochainComplexXIso k k rfl).inv) (zero_add _))) = _
  rw [HomComplexSections.nativeHomComplexSectionsIso_fromSingle, ResolutionExtensionSections.resolutionMapExtendXIso_natCast]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, ConcreteCategory.comp_apply]
  change ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extendXIso
    ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)).inv
      ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (R.cochainComplexXIso k k rfl).hom
        (SectionCoordinates.nativeSheafHomGlobalEquiv (R.cochainComplex.X k)
          (f ≫ (R.cochainComplexXIso k k rfl).inv))) = _
  rw [← SectionCoordinates.nativeSheafHomGlobalEquiv_naturality]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem nativeResolutionSection_closed (n : ℕ)
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ R.cocomplex.X (n + 1))
    (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0) :
    (FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).d (n + 1) (n + 2)
      (SectionCoordinates.nativeSheafHomGlobalEquiv (R.cocomplex.X (n + 1)) f) = 0 := by
  change (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (R.cocomplex.d (n + 1) (n + 2))
    (SectionCoordinates.nativeSheafHomGlobalEquiv (R.cocomplex.X (n + 1)) f) = 0
  rw [← SectionCoordinates.nativeSheafHomGlobalEquiv_naturality, hf, map_zero]

def nativeResolutionCocycle (n : ℕ)
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ R.cocomplex.X (n + 1))
    (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0) :
    Cocycle ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
      (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)) R.cochainComplex (n + 1) :=
  Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso (n + 1) (n + 1) rfl).inv)
    (zero_add _) (n + 2 : ℕ) (by omega)
      (by
        rw [R.cochainComplex_d _ _ (n + 1) (n + 2) (by omega) (by omega)]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])

theorem nativeResolutionCocycle_extMk (n : ℕ)
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ R.cocomplex.X (n + 1))
    (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0) :
    R.extAddEquivCohomologyClass (R.extMk f (n + 2) rfl hf) =
      CohomologyClass.mk (nativeResolutionCocycle R n f hf) :=
  R.extEquivCohomologyClass_extMk f (n + 2) rfl hf

end

section

/-! Actual resolution cocycles under the native sheaf-cohomology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open _root_.CochainComplex _root_.CochainComplex.HomComplex
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  (R : InjectiveResolution F) (n : ℕ)
  (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ R.cocomplex.X (n + 1))
  (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0)

local instance nativeResolutionHomology_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

theorem nativeResolutionHomology_coordinates :
    HomologicalComplex.homologyMap (nativeResolutionSectionsIso R).hom ((n + 1 : ℕ) : ℤ)
      ((homologyAddEquiv ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
        (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)) R.cochainComplex ((n + 1 : ℕ) : ℤ)).symm
          (R.extAddEquivCohomologyClass (R.extMk f (n + 2) rfl hf))) =
      Abelian.CycleCoordinates.abelianIntegerCycleClass
        ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extend ComplexShape.embeddingUpNat)
        ((n + 1 : ℕ) : ℤ)
        (((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extendXIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f (n + 1))).inv
            (SectionCoordinates.nativeSheafHomGlobalEquiv (R.cocomplex.X (n + 1)) f))
        (ExtendedCycleCoordinates.extendedCycle_closed _ n _ (nativeResolutionSection_closed R n f hf)) := by
  rw [nativeResolutionCocycle_extMk, HomComplexCycleCoordinates.homComplexCohomologyClass_coordinates]
  let z := nativeResolutionCocycle R n f hf
  have he : (nativeResolutionSectionsIso R).hom.f ((n + 1 : ℕ) : ℤ) z.val =
      ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f (n + 1))).inv
          (SectionCoordinates.nativeSheafHomGlobalEquiv (R.cocomplex.X (n + 1)) f) :=
    nativeResolutionSectionsIso_fromSingle R (n + 1) f
  have hy : ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extend ComplexShape.embeddingUpNat).d
      ((n + 1 : ℕ) : ℤ) (((n + 1 : ℕ) : ℤ) + 1)
      ((nativeResolutionSectionsIso R).hom.f ((n + 1 : ℕ) : ℤ) z.val) = 0 := by
    rw [he]
    exact ExtendedCycleCoordinates.extendedCycle_closed _ n _ (nativeResolutionSection_closed R n f hf)
  have hm := Abelian.CycleCoordinates.abelianIntegerCycleClass_map ((n + 1 : ℕ) : ℤ)
    (nativeResolutionSectionsIso R).hom z.val (HomComplexCycleCoordinates.homComplexCocycle_closed _ _ _ z) hy
  simpa only [he] using hm

theorem nativeResolutionHomology_positive_coordinates :
    ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f (n + 1))).hom
      (HomologicalComplex.homologyMap (nativeResolutionSectionsIso R).hom ((n + 1 : ℕ) : ℤ)
        ((homologyAddEquiv ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
          (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)) R.cochainComplex ((n + 1 : ℕ) : ℤ)).symm
            (R.extAddEquivCohomologyClass (R.extMk f (n + 2) rfl hf)))) =
      (FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).homologyπ (n + 1)
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n (FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex)
          (SectionCoordinates.nativeSheafHomGlobalEquiv (R.cocomplex.X (n + 1)) f)
          (nativeResolutionSection_closed R n f hf)) := by
  rw [nativeResolutionHomology_coordinates]
  exact ExtendedCycleCoordinates.extendedCycleClass_coordinates _ n _ (nativeResolutionSection_closed R n f hf)

end

section

/-! The existing native injective comparison sends actual cocycles to their actual Ext classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf Opposite
open _root_.CochainComplex _root_.CochainComplex.HomComplex
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)

local instance nativeInjectiveRepresentatives_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

theorem nativeExtResolutionEquiv_extMk
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ (injectiveResolution F).cocomplex.X (n + 1))
    (hf : f ≫ (injectiveResolution F).cocomplex.d (n + 1) (n + 2) = 0) :
    ExtResolutionCoordinates.nativeExtResolutionEquiv F n ((injectiveResolution F).extMk f (n + 2) rfl hf) =
      (FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex).homologyπ (n + 1)
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n (FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex)
          (SectionCoordinates.nativeSheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1)) f)
          (nativeResolutionSection_closed (injectiveResolution F) n f hf)) := by
  let R := injectiveResolution F
  let a := (homologyAddEquiv ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
    (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)) R.cochainComplex ((n + 1 : ℕ) : ℤ)).symm
      (R.extAddEquivCohomologyClass (R.extMk f (n + 2) rfl hf))
  change ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f (n + 1))).hom
      (HomologicalComplex.homologyMap
        (ResolutionExtensionSections.resolutionMapExtendIso (G := SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) R.cocomplex).hom
        ((n + 1 : ℕ) : ℤ)
        (HomologicalComplex.homologyMap (HomComplexSections.nativeHomComplexSectionsIso R.cochainComplex).hom
          ((n + 1 : ℕ) : ℤ) a)) = _
  have hm := ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp
    (HomComplexSections.nativeHomComplexSectionsIso R.cochainComplex).hom
    (ResolutionExtensionSections.resolutionMapExtendIso (G := SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) R.cocomplex).hom
    ((n + 1 : ℕ) : ℤ)) a
  change HomologicalComplex.homologyMap (nativeResolutionSectionsIso R).hom
      ((n + 1 : ℕ) : ℤ) a =
    HomologicalComplex.homologyMap
      (ResolutionExtensionSections.resolutionMapExtendIso (G := SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) R.cocomplex).hom
      ((n + 1 : ℕ) : ℤ)
      (HomologicalComplex.homologyMap (HomComplexSections.nativeHomComplexSectionsIso R.cochainComplex).hom
        ((n + 1 : ℕ) : ℤ) a) at hm
  exact (congrArg (((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f (n + 1))).hom) hm.symm).trans
    (nativeResolutionHomology_positive_coordinates R n f hf)

theorem nativeInjectiveCohomologyIso_extMk
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ (injectiveResolution F).cocomplex.X (n + 1))
    (hf : f ≫ (injectiveResolution F).cocomplex.d (n + 1) (n + 2) = 0) :
    (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom
      ((FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex).homologyπ (n + 1)
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n (FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex)
          (SectionCoordinates.nativeSheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1)) f)
          (nativeResolutionSection_closed (injectiveResolution F) n f hf))) =
      (injectiveResolution F).extMk f (n + 2) rfl hf := by
  rw [← nativeExtResolutionEquiv_extMk F n f hf,
    ← ExtResolutionCoordinates.nativeInjectiveCohomologyIso_inv_coordinates]
  exact (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).inv_hom_id_apply _

end

/-! The native injective comparison on actual sections over the whole space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

theorem nativeSheafHomGlobalEquiv_symm_top (s : F.obj.obj (op (⊤ : Opens X))) :
    SectionCoordinates.nativeSheafHomGlobalEquiv F ((Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv F).symm s) =
      (CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
        AddCommGrpCat.{0} isTerminalTop).inv.app F s := by
  let e := (CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{0} isTerminalTop).app F
  apply (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom (SectionCoordinates.nativeSheafHomGlobalEquiv F ((Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv F).symm s)) = e.hom (e.inv s)
  rw [e.inv_hom_id_apply]
  exact (SectionCoordinates.nativeSheafHomGlobalEquiv_top F ((Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv F).symm s)).trans
    ((Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv F).apply_symm_apply s)

variable (n : ℕ)
  (s : ((injectiveResolution F).cocomplex.X (n + 1)).obj.obj (op (⊤ : Opens X)))
  (hs : ((injectiveResolution F).cocomplex.d (n + 1) (n + 2)).hom.app
    (op (⊤ : Opens X)) s = 0)

include hs in
theorem nativeResolutionTopSection_closed :
    (FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex).d (n + 1) (n + 2)
      ((GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv.f (n + 1) s) = 0 := by
  let f := (Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1))).symm s
  have hf : f ≫ (injectiveResolution F).cocomplex.d (n + 1) (n + 2) = 0 := by
    apply (Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 2))).injective
    rw [Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv_naturality, map_zero]
    exact ((Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1))).apply_symm_apply s ▸ hs)
  have he := nativeSheafHomGlobalEquiv_symm_top ((injectiveResolution F).cocomplex.X (n + 1)) s
  change SectionCoordinates.nativeSheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1)) f =
    (GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv.f (n + 1) s at he
  exact he ▸ nativeResolutionSection_closed (injectiveResolution F) n f hf

theorem nativeInjectiveCohomologyIso_sectionClass :
    (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom
      ((FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex).homologyπ (n + 1)
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n (FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex)
          ((GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv.f (n + 1) s)
          (nativeResolutionTopSection_closed F n s hs))) =
      Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (injectiveResolution F) (n + 1) s hs := by
  let f := (Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1))).symm s
  have hf : f ≫ (injectiveResolution F).cocomplex.d (n + 1) (n + 2) = 0 := by
    apply (Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 2))).injective
    rw [Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv_naturality, map_zero]
    exact ((Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1))).apply_symm_apply s ▸ hs)
  have he := nativeSheafHomGlobalEquiv_symm_top ((injectiveResolution F).cocomplex.X (n + 1)) s
  change SectionCoordinates.nativeSheafHomGlobalEquiv ((injectiveResolution F).cocomplex.X (n + 1)) f =
    (GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv.f (n + 1) s at he
  have h := nativeInjectiveCohomologyIso_extMk F n f hf
  change _ = (injectiveResolution F).extMk f (n + 2) rfl hf
  simpa only [he] using h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ResolutionInjective
