import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.EndomorphismRing
import Mathlib.CategoryTheory.Endomorphism

/-! # Endomorphism Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Units of the endomorphism ring are precisely automorphisms of the group object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.endRingMultiplicativeEquiv : A.EndRing ≃* End A.groupObject where
  toFun f := f.toMul
  invFun := Additive.ofMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def Abelian.Schemes.AbelianScheme.endRingUnitsEquivAut : A.EndRingˣ ≃* Aut A.groupObject :=
  (Units.mapEquiv A.endRingMultiplicativeEquiv).trans (Aut.unitsEndEquivAut A.groupObject)

def Abelian.Schemes.AbelianScheme.groupIsoOfSchemeIso (e : A.scheme ≅ A.scheme) [IsMonHom e.hom] : Aut A.groupObject where
  hom := Grp.homMk e.hom
  inv := Grp.homMk e.inv
  hom_inv_id := Grp.hom_ext _ _ e.hom_inv_id
  inv_hom_id := Grp.hom_ext _ _ e.inv_hom_id

def Abelian.Schemes.AbelianScheme.endRingUnitOfIso (e : A.scheme ≅ A.scheme) [IsMonHom e.hom] : A.EndRingˣ :=
  A.endRingUnitsEquivAut.symm (A.groupIsoOfSchemeIso e)

@[simp] theorem Abelian.Schemes.AbelianScheme.endRingUnitOfIso_hom (e : A.scheme ≅ A.scheme) [IsMonHom e.hom] :
    (A.endRingUnitOfIso e).val.toMul.hom.hom = e.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
