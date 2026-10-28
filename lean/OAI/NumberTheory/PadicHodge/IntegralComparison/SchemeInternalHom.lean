import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.Additive

/-! # Scheme Internal Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom

noncomputable section

/-! The genuine sheaf of module homomorphisms, contravariantly functorial
in its source, and its global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction

universe u

variable {X : Scheme.{u}}

def functor (N : X.Modules) : X.Modulesᵒᵖ ⥤ X.Modules where
  obj M := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M.unop N
  map f := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f.unop (𝟙 N)
  map_id M := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap_id M.unop N
  map_comp f g := by
    simpa only [Category.id_comp, unop_comp] using ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap_comp f.unop g.unop (𝟙 N) (𝟙 N)

instance functor_additive (N : X.Modules) : (functor N).Additive where
  map_add {M P} f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    change q.val.app V ((f.unop.app V.unop.left).hom m + (g.unop.app V.unop.left).hom m) =
      q.val.app V ((f.unop.app V.unop.left).hom m) + q.val.app V ((g.unop.app V.unop.left).hom m)
    exact map_add _ _ _

def fromTop (M N : X.Modules) (q : M.over ⊤ ⟶ N.over ⊤) : M ⟶ N where
  val :=
    { app U := q.val.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))
      naturality {U V} f :=
        q.val.naturality
          (Over.homMk f.unop :
            Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
              Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))).op }

def overTopEquiv (M N : X.Modules) : (M ⟶ N) ≃ (M.over ⊤ ⟶ N.over ⊤) where
  toFun f := f.over ⊤
  invFun := fromTop M N
  left_inv f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv q := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    cases U with
    | op U =>
      cases U
      rfl

def globalSectionsEquiv (M N : X.Modules) :
    (M ⟶ N) ≃+ (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).val.obj (op ⊤) where
  toEquiv := (overTopEquiv M N).trans (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomOverEquiv M N ⊤).symm
  map_add' f g := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    rfl

def sections : X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙ forget₂ _ AddCommGrpCat

instance sections_additive : (sections (X := X)).Additive where
  map_add {_M _N} _f _g := rfl

def globalSectionsIso (N : X.Modules) :
    preadditiveYoneda.obj N ≅ functor N ⋙ sections :=
  NatIso.ofComponents (fun M => (globalSectionsEquiv M.unop N).toAddCommGrpIso) (by
    intro M P f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    apply Subtype.ext
    apply NatTrans.ext
    funext U
    ext m
    rfl)

def complex {ι : Type*} (c : ComplexShape ι) (N : X.Modules)
    (K : HomologicalComplex X.Modulesᵒᵖ c) : HomologicalComplex X.Modules c :=
  ((functor N).mapHomologicalComplex c).obj K

def complexSectionsIso {ι : Type*} (c : ComplexShape ι) (N : X.Modules)
    (K : HomologicalComplex X.Modulesᵒᵖ c) :
    ((preadditiveYoneda.obj N).mapHomologicalComplex c).obj K ≅
      (sections.mapHomologicalComplex c).obj (complex c N K) :=
  (NatIso.mapHomologicalComplex (globalSectionsIso N) c).app K

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
