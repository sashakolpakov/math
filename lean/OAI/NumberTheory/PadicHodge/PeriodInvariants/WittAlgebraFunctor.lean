import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Witt Algebra Functor -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraFunctor

noncomputable section

/-! # Witt algebras and their actual zeroth-coefficient reduction as functors -/

open _root_.CategoryTheory

section Maps

variable (p : ℕ) [Fact p.Prime] (S : Type*) [CommRing S]
  {T U : Type*} [CommRing T] [CommRing U] [Algebra S T] [Algebra S U]

local instance wittAlgebra : Algebra (WittVector p S) (WittVector p T) :=
  (WittVector.map (algebraMap S T)).toAlgebra

local instance residueAlgebra : Algebra (WittVector p S) T :=
  ((algebraMap S T).comp (WittVector.constantCoeff (p := p))).toAlgebra

def map (f : T →ₐ[S] U) : WittVector p T →ₐ[WittVector p S] WittVector p U where
  __ := WittVector.map f.toRingHom
  commutes' w := by
    apply WittVector.ext
    intro n
    change f (algebraMap S T (w.coeff n)) = algebraMap S U (w.coeff n)
    exact f.commutes _

theorem map_coeff (f : T →ₐ[S] U) (w : WittVector p T) (n : ℕ) :
    (WittAlgebraFunctor.map p S f w).coeff n = f (w.coeff n) := rfl

def residueMap (f : T →ₐ[S] U) : T →ₐ[WittVector p S] U where
  __ := f.toRingHom
  commutes' w := f.commutes (w.coeff 0)

def reduction : WittVector p T →ₐ[WittVector p S] T where
  __ := WittVector.constantCoeff
  commutes' _ := rfl

theorem reduction_apply (w : WittVector p T) : reduction p S w = w.coeff 0 := rfl

theorem reduction_naturality (f : T →ₐ[S] U) (w : WittVector p T) :
    reduction p S (WittAlgebraFunctor.map p S f w) = residueMap p S f (reduction p S w) := rfl

end Maps

attribute [local instance] wittAlgebra residueAlgebra

universe u
variable (p : ℕ) [Fact p.Prime] (S : Type u) [CommRing S]

def functor : CommAlgCat.{u} S ⥤ CommAlgCat.{u} (WittVector p S) where
  obj T := CommAlgCat.of (WittVector p S) (WittVector p T)
  map f := CommAlgCat.ofHom (WittAlgebraFunctor.map p S f.hom)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro w
    apply WittVector.ext
    intro n
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro w
    apply WittVector.ext
    intro n
    rfl

def residueFunctor : CommAlgCat.{u} S ⥤ CommAlgCat.{u} (WittVector p S) where
  obj T := CommAlgCat.of (WittVector p S) T
  map f := CommAlgCat.ofHom (residueMap p S f.hom)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

def reductionNat : functor p S ⟶ residueFunctor p S where
  app T := CommAlgCat.ofHom (reduction p S)
  naturality {T U} f := by
    apply ConcreteCategory.hom_ext
    intro w
    rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraFunctor
