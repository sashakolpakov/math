import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Limits.IsLimit

/-! # Cone Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ConeSections.ModuleConeSections

noncomputable section

/-! # A module limit cone represents coefficient-linear sections -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  {F : C ⥤ ModuleCat.{w} R} (t : Cone F) (ht : IsLimit t)

def homLinearEquiv (M : ModuleCat.{w} R) :
    (M ⟶ t.pt) ≃ₗ[R] ((Functor.const C).obj M ⟶ F) where
  toEquiv := ht.homEquiv
  map_add' f g := by
    apply NatTrans.ext
    funext Q
    exact Preadditive.add_comp _ _ _ f g (t.π.app Q)
  map_smul' r f := by
    apply NatTrans.ext
    funext Q
    exact Linear.smul_comp _ _ _ r f (t.π.app Q)

def sectionsEquiv : ((Functor.const C).obj (ModuleCat.of R R) ⟶ F) ≃ₗ[R] t.pt :=
  (ModuleConeSections.homLinearEquiv R t ht (ModuleCat.of R R)).symm.trans
    ((ModuleCat.homLinearEquiv (R := R) (S := R)).trans (LinearMap.ringLmapEquivSelf R R t.pt))

theorem sectionsEquiv_eval (s : (Functor.const C).obj (ModuleCat.of R R) ⟶ F) (Q : C) :
    t.π.app Q (sectionsEquiv R t ht s) = s.app Q (1 : R) :=
  ConcreteCategory.congr_hom (ht.homEquiv_symm_π_app s Q) (1 : R)

theorem sectionsEquiv_symm_eval (x : t.pt) (Q : C) :
    ((sectionsEquiv R t ht).symm x).app Q (1 : R) = t.π.app Q x := by
  have h := sectionsEquiv_eval R t ht ((sectionsEquiv R t ht).symm x) Q
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

include ht in
theorem ext {x y : t.pt} (h : ∀ Q, t.π.app Q x = t.π.app Q y) : x = y := by
  let ex : ModuleCat.of R R ⟶ t.pt := ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R R t.pt).symm x)
  let ey : ModuleCat.of R R ⟶ t.pt := ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R R t.pt).symm y)
  have he : ex = ey := ht.hom_ext (by
    intro Q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change t.π.app Q (r • x) = t.π.app Q (r • y)
    rw [(t.π.app Q).hom.map_smul, (t.π.app Q).hom.map_smul, h Q])
  have h1 := ConcreteCategory.congr_hom he 1
  change (1 : R) • x = (1 : R) • y at h1
  simpa only [one_smul] using h1

variable {G : C ⥤ ModuleCat.{w} R} (s : Cone G) (hs : IsLimit s)
  (f : F ⟶ G) (g : t.pt ⟶ s.pt)
  (hg : ∀ Q, g ≫ s.π.app Q = t.π.app Q ≫ f.app Q)

include hg in
theorem naturality (x : (Functor.const C).obj (ModuleCat.of R R) ⟶ F) :
    sectionsEquiv R s hs (x ≫ f) = g (sectionsEquiv R t ht x) := by
  apply ModuleConeSections.ext R s hs
  intro Q
  rw [sectionsEquiv_eval]
  have h := ConcreteCategory.congr_hom (hg Q) (sectionsEquiv R t ht x)
  change s.π.app Q (g (sectionsEquiv R t ht x)) =
    f.app Q (t.π.app Q (sectionsEquiv R t ht x)) at h
  rw [sectionsEquiv_eval] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ConeSections.ModuleConeSections
