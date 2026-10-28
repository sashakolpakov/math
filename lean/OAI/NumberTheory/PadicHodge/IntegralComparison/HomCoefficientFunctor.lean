import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Hom Coefficient Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor

noncomputable section

/-! Ordinary linear Hom with presheaf coefficients, as an additive
contravariant functor. Resolution maps and homotopies therefore act
on the whole coefficient presheaf, before taking Čech cohomology. -/
open _root_.CategoryTheory Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type v} [Category C] (R : Type u) [CommRing R]
  (P : C ⥤ ModuleCat.{u} R)

def homPresheaf (M : ModuleCat.{u} R) : C ⥤ ModuleCat.{u} R where
  obj a := ModuleCat.of R (M →ₗ[R] P.obj a)
  map f := ModuleCat.ofHom
    { toFun := fun φ => (P.map f).hom.comp φ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_id a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp

def precomp {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    homPresheaf R P N ⟶ homPresheaf R P M where
  app a := ModuleCat.ofHom
    { toFun := fun φ => φ.comp f.hom
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    rfl

def functor : (ModuleCat.{u} R)ᵒᵖ ⥤ (C ⥤ ModuleCat.{u} R) where
  obj M := homPresheaf R P M.unop
  map f := precomp R P f.unop
  map_id M := by
    apply NatTrans.ext
    funext a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    rfl

instance additive : (functor R P).Additive where
  map_add {M N} f g := by
    apply NatTrans.ext
    funext a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change M.unop →ₗ[R] P.obj a at φ
    apply LinearMap.ext
    intro x
    change φ (f.unop.hom x + g.unop.hom x) = φ (f.unop.hom x) + φ (g.unop.hom x)
    exact map_add φ _ _

variable {ι : Type*} {c : ComplexShape ι}

def complex (K : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (C ⥤ ModuleCat.{u} R) c.symm :=
  ((functor R P).mapHomologicalComplex c.symm).obj K.op

def map {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) :
    complex R P L ⟶ complex R P K :=
  ((functor R P).mapHomologicalComplex c.symm).map
    ((HomologicalComplex.opFunctor (ModuleCat.{u} R) c).map f.op)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor
