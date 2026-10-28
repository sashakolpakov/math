import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Group Objects -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Abelian-scheme homomorphisms as morphisms in the category of group objects, with their additive group structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g h : ℕ}

abbrev Schemes.AbelianScheme.groupObject (A : Schemes.AbelianScheme g S) : Grp (Over S) := ⟨A.scheme⟩

instance Schemes.AbelianScheme.groupObject_commutative (A : Schemes.AbelianScheme g S) : IsCommMonObj A.groupObject :=
  inferInstanceAs (IsCommMonObj (⟨A.scheme⟩ : Grp (Over S)))

instance Schemes.AbelianScheme.groupHomCommGroup (A : Schemes.AbelianScheme g S) (B : Schemes.AbelianScheme h S) :
    CommGroup (A.groupObject ⟶ B.groupObject) := CategoryTheory.Hom.commGroup

def Schemes.AbelianScheme.groupHomEquiv (A : Schemes.AbelianScheme g S) (B : Schemes.AbelianScheme h S) :
    (A.groupObject ⟶ B.groupObject) ≃ {f : A.scheme ⟶ B.scheme // IsMonHom f} where
  toFun f := ⟨f.hom.hom, inferInstance⟩
  invFun f := by
    have : IsMonHom f.val := f.property
    exact Grp.homMk f.val
  left_inv f := by ext; rfl
  right_inv f := by apply Subtype.ext; rfl

abbrev Schemes.AbelianScheme.AddHom (A : Schemes.AbelianScheme g S) (B : Schemes.AbelianScheme h S) :=
  Additive (A.groupObject ⟶ B.groupObject)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
