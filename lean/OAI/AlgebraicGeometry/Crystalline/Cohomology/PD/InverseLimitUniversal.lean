import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit
import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Inverse Limit Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitUniversal.PDInverseLimitUniversal

noncomputable section

/-!
# The categorical universal property of compatible PD sections

The existing ring of compatible sections, with its native Witt action,
is the categorical inverse limit of the actual ambient module diagram.
This relates the explicit completed PD constructions to limits used by
global sections, without introducing a separate completion model.
-/

open _root_.CategoryTheory Limits Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]

local notation "W" => WittVector p k

def ambientModules : Thickening.AffinePDThickening p k B ⥤ ModuleCat.{u} W where
  obj S := ModuleCat.of W S.ring
  map f := ModuleCat.ofHom f.hom.toLinearMap

variable (F : ℕᵒᵖ ⥤ Thickening.AffinePDThickening p k B)

def cone : Cone (F ⋙ ambientModules p k B) where
  pt := ModuleCat.of W (InverseLimit.PDInverseLimit.Ring p k B F)
  π :=
    { app n := ModuleCat.ofHom (InverseLimit.PDInverseLimit.eval p k B F n.unop).toLinearMap
      naturality := by
        intro n m f
        apply ModuleCat.hom_ext
        ext x
        exact (InverseLimit.PDInverseLimit.eval_compatible p k B F m.unop n.unop (leOfHom f.unop) x).symm }

def lift (s : Cone (F ⋙ ambientModules p k B)) : s.pt ⟶ (cone p k B F).pt :=
  ModuleCat.ofHom
    { toFun x :=
        ⟨fun n => s.π.app (op n) x, fun n m h => by
          have he := ConcreteCategory.congr_hom (s.w (homOfLE h).op) x
          exact he⟩
      map_add' x y := InverseLimit.PDInverseLimit.ext p k B F (fun n => (s.π.app (op n)).hom.map_add x y)
      map_smul' w x := InverseLimit.PDInverseLimit.ext p k B F (fun n => (s.π.app (op n)).hom.map_smul w x) }

def isLimit : IsLimit (cone p k B F) where
  lift := PDInverseLimitUniversal.lift p k B F
  fac _ _ := by ext; rfl
  uniq s m hm := by
    apply ModuleCat.hom_ext
    ext x
    apply InverseLimit.PDInverseLimit.ext p k B F
    intro n
    exact ConcreteCategory.congr_hom (hm (op n)) x

def limitIso : ModuleCat.of W (InverseLimit.PDInverseLimit.Ring p k B F) ≅ limit (F ⋙ ambientModules p k B) :=
  (PDInverseLimitUniversal.isLimit p k B F).conePointUniqueUpToIso (limit.isLimit _)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitUniversal.PDInverseLimitUniversal
