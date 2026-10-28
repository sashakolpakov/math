import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # Presheaf Product -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PresheafProduct.PresheafProductLocalization

noncomputable section

/-!
# Localization of finite products of module presheaves

The categorical product restriction map is a localization whenever every
component restriction map is. The comparison uses the actual evaluation
and module-product isomorphisms.
-/

open _root_.CategoryTheory Limits

universe u v

variable (R : Type u) [CommRing R] (S : Submonoid R)
  {D : Type v} [Category D] {α : Type u} [Finite α]
  (F : α → D ⥤ ModuleCat.{u} R)

def sectionsIso (V : D) :
    (∏ᶜ F).obj V ≅ ModuleCat.of R (∀ i, (F i).obj V) :=
  piObjIso F V ≪≫ ModuleCat.piIsoPi _

theorem sectionsIso_projection (V : D) (i : α) :
    (sectionsIso R F V).hom ≫ ModuleCat.ofHom (LinearMap.proj i) = (Pi.π F i).app V := by
  simp only [sectionsIso, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype, piObjIso_hom_comp_π]

theorem sectionsIso_naturality {V W : D} (f : V ⟶ W) :
    (∏ᶜ F).map f ≫ (sectionsIso R F W).hom =
      (sectionsIso R F V).hom ≫ ModuleCat.ofHom
        (LinearMap.pi fun i => ((F i).map f).hom.comp (LinearMap.proj i)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have h := (Pi.π F i).naturality f
  have hV := sectionsIso_projection R F V i
  have hW := sectionsIso_projection R F W i
  exact (congrArg (fun a => (a : (∏ᶜ F).obj V ⟶ (F i).obj W).hom x)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => (∏ᶜ F).map f ≫ a) hW).trans
        (h.trans (congrArg (fun a => a ≫ (F i).map f) hV.symm)))))

theorem isLocalizedModule {V W : D} (f : V ⟶ W)
    [∀ i, IsLocalizedModule S ((F i).map f).hom] :
    IsLocalizedModule S ((∏ᶜ F).map f).hom := by
  rw [← IsLocalizedModule.comp_iff_of_bijective_left S
    (sectionsIso R F W).hom.hom (ConcreteCategory.bijective_of_isIso _),
    ← ModuleCat.hom_comp, sectionsIso_naturality R F f, ModuleCat.hom_comp,
    IsLocalizedModule.comp_iff_of_bijective_right S
      (sectionsIso R F V).hom.hom (ConcreteCategory.bijective_of_isIso _)]
  change IsLocalizedModule S (LinearMap.pi fun i => ((F i).map f).hom.comp (LinearMap.proj i))
  exact IsLocalizedModule.pi S (fun i => ((F i).map f).hom)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PresheafProduct.PresheafProductLocalization
