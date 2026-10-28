import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Countable Module Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CountableModuleProduct

noncomputable section

/-!
# IntegralComparison: countable products of coefficient modules are exact
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]

def functor : (Discrete ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj F := ModuleCat.of R (∀ n, F.obj ⟨n⟩)
  map α := ModuleCat.ofHom
    { toFun := fun x n => α.app ⟨n⟩ (x n)
      map_add' := fun x y => funext (fun n => (α.app ⟨n⟩).hom.map_add (x n) (y n))
      map_smul' := fun r x => funext (fun n => (α.app ⟨n⟩).hom.map_smul r (x n)) }
  map_id _F := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))
  map_comp _α _β := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))

instance additive : (functor R).Additive where
  map_add := by intros; rfl

def cone (F : Discrete ℕ ⥤ ModuleCat.{u} R) : Cone F where
  pt := (functor R).obj F
  π := Discrete.natTrans (fun n => ModuleCat.ofHom (LinearMap.proj n.as))

def isLimit (F : Discrete ℕ ⥤ ModuleCat.{u} R) : IsLimit (cone R F) where
  lift s := ModuleCat.ofHom (LinearMap.pi (fun n => (s.π.app ⟨n⟩).hom))
  fac s n := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))
  uniq s a ha := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    exact congrArg (fun g : s.pt ⟶ F.obj ⟨n⟩ => g x) (ha ⟨n⟩)

def componentIso (F : Discrete ℕ ⥤ ModuleCat.{u} R) : limit F ≅ (functor R).obj F :=
  limit.isoLimitCone ⟨cone R F, isLimit R F⟩

theorem componentIso_projection (F : Discrete ℕ ⥤ ModuleCat.{u} R) (n : ℕ) :
    (componentIso R F).hom ≫ ModuleCat.ofHom (LinearMap.proj n) = limit.π F ⟨n⟩ :=
  limit.isoLimitCone_hom_π ⟨cone R F, isLimit R F⟩ ⟨n⟩

def iso : lim (J := Discrete ℕ) (C := ModuleCat.{u} R) ≅ functor R :=
  NatIso.ofComponents (componentIso R) (by
    intro F G α
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    have h₁ := congrArg (fun g : limit G ⟶ G.obj ⟨n⟩ => g ((lim.map α) x)) (componentIso_projection R G n)
    have h₂ := congrArg (fun g : limit F ⟶ F.obj ⟨n⟩ => α.app ⟨n⟩ (g x)) (componentIso_projection R F n)
    have h := congrArg (fun g : limit F ⟶ G.obj ⟨n⟩ => g x) (limMap_π α ⟨n⟩)
    exact h₁.trans (h.trans h₂.symm))

instance preservesFiniteLimits : PreservesFiniteLimits (functor R) :=
  preservesFiniteLimits_of_natIso (iso R)

instance preservesFiniteColimits : PreservesFiniteColimits (functor R) :=
  preservesFiniteColimits_of_natIso (iso R)

instance preservesHomology : (functor R).PreservesHomology := by infer_instance

def projection (n : ℕ) : functor R ⟶ (evaluation (Discrete ℕ) (ModuleCat.{u} R)).obj ⟨n⟩ where
  app _F := ModuleCat.ofHom (LinearMap.proj n)
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CountableModuleProduct
