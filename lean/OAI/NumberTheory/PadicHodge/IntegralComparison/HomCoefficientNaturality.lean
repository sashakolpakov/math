import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor

/-! # Hom Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientNaturality

noncomputable section

/-! Coefficient maps and coefficient isomorphisms on the ordinary
Hom presheaf, with all resolution maps and differentials retained. -/
open _root_.CategoryTheory Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor
variable {C : Type v} [Category C] (R : Type u) [CommRing R]
  {P Q : C ⥤ ModuleCat.{u} R} (a : P ⟶ Q)

def postcomp (M : ModuleCat.{u} R) : HomCoefficientFunctor.homPresheaf R P M ⟶ HomCoefficientFunctor.homPresheaf R Q M where
  app c := ModuleCat.ofHom
    { toFun := fun φ => (a.app c).hom.comp φ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  naturality c d f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change M →ₗ[R] P.obj c at φ
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (a.naturality f) (φ x)

def transformation : HomCoefficientFunctor.functor R P ⟶ HomCoefficientFunctor.functor R Q where
  app M := postcomp R a M.unop
  naturality M N f := by
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    rfl

def iso (e : P ≅ Q) : HomCoefficientFunctor.functor R P ≅ HomCoefficientFunctor.functor R Q where
  hom := transformation R e.hom
  inv := transformation R e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change M.unop →ₗ[R] P.obj c at φ
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (congrArg (fun z => z.app c) e.hom_inv_id) (φ x)
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change M.unop →ₗ[R] Q.obj c at φ
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (congrArg (fun z => z.app c) e.inv_hom_id) (φ x)

def complexMap {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) : HomCoefficientFunctor.complex R P K ⟶ HomCoefficientFunctor.complex R Q K :=
  ((transformation R a).mapHomologicalComplex c.symm).app K.op

def complexIso {ι : Type*} {c : ComplexShape ι}
    (e : P ≅ Q) (K : HomologicalComplex (ModuleCat.{u} R) c) :
    HomCoefficientFunctor.complex R P K ≅ HomCoefficientFunctor.complex R Q K :=
  (NatIso.mapHomologicalComplex (iso R e) c.symm).app K.op

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientNaturality
