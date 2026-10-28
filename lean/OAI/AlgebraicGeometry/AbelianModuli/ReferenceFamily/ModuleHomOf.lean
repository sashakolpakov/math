import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Module Hom Of -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleHomOf

noncomputable section

section

/-! Forgetting an actual module sheaf to its abelian sheaf preserves
finite colimits. This supplies genuine local lifts through epimorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem preservesColimit_after_reflector
    {C : Type*} {D : Type*} {E : Type*} {J : Type*}
    [Category* C] [Category* D] [Category* E] [Category* J]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [IsIso adj.counit]
    (H : D ⥤ E) (K : J ⥤ D) [HasColimit (K ⋙ G)]
    [PreservesColimit (K ⋙ G) F] [PreservesColimit (K ⋙ G) (F ⋙ H)] :
    PreservesColimit K H := by
  have hF := isColimitOfPreserves F (colimit.isColimit (K ⋙ G))
  have hFH := isColimitOfPreserves (F ⋙ H) (colimit.isColimit (K ⋙ G))
  let : PreservesColimit ((K ⋙ G) ⋙ F) H :=
    preservesColimit_of_preserves_colimit_cocone hF hFH
  exact preservesColimit_of_iso_diagram H
    (Functor.associator K G F ≪≫ Functor.isoWhiskerLeft K (asIso adj.counit) ≪≫ Functor.rightUnitor K)

theorem moduleSheaf_toSheaf_preservesFiniteColimits (X : Scheme.{0}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{0} X.ringCatSheaf) := by
  let F := PresheafOfModules.sheafification.{0} (𝟙 X.ringCatSheaf.obj)
  let H := SheafOfModules.toSheaf.{0} X.ringCatSheaf
  let adj := PresheafOfModules.sheafificationAdjunction.{0} (𝟙 X.ringCatSheaf.obj)
  have : PreservesFiniteColimits (F ⋙ H) :=
    comp_preservesFiniteColimits (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (presheafToSheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{0})
  constructor
  intro J _ _
  constructor
  intro K
  exact preservesColimit_after_reflector adj H K

theorem moduleSheaf_toSheaf_epi {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N) [hf : Epi f] :
    Epi ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).map f) := by
  let : PreservesFiniteColimits (SheafOfModules.toSheaf.{0} X.ringCatSheaf) :=
    moduleSheaf_toSheaf_preservesFiniteColimits X
  let h : (SheafOfModules.toSheaf.{0} X.ringCatSheaf).PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
  exact @h.preserves M N f hf

end

/-! A scalar-compatible map of the original underlying abelian sheaves
is an actual morphism of algebraic module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

def moduleHomOfAbelian {X : Scheme.{0}} {M N : X.Modules}
    (f : (SheafOfModules.toSheaf X.ringCatSheaf).obj M ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj N)
    (h : ∀ (U : X.Opens) (a : Γ(X, U)) (m : Γ(M, U)),
      f.hom.app (op U) (a • m) = a • (show Γ(N, U) from f.hom.app (op U) m)) : M ⟶ N where
  val := {
    app U := ModuleCat.ofHom {
      toFun := f.hom.app U
      map_add' m n := (f.hom.app U).hom.map_add m n
      map_smul' a m := h U.unop a m }
    naturality := by
      intro U V t
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      exact ConcreteCategory.congr_hom (f.hom.naturality t) m }

theorem moduleHomOfAbelian_underlying {X : Scheme.{0}} {M N : X.Modules}
    (f : (SheafOfModules.toSheaf X.ringCatSheaf).obj M ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj N)
    (h : ∀ (U : X.Opens) (a : Γ(X, U)) (m : Γ(M, U)),
      f.hom.app (op U) (a • m) = a • (show Γ(N, U) from f.hom.app (op U) m)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (moduleHomOfAbelian f h) = f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleHomOf
