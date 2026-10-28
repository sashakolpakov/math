import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Family Lift Factorization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FamilyLiftFactorization.Construction

noncomputable section

/-! Factorizations of a parameter map and morphisms into a family over
that parameter have the same actual scheme maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {S : Scheme.{u}} (T : Over S) (M : Over T.left)

def compositeFamily : Over S := Over.mk (M.hom ≫ T.hom)

def compositeFamilyMap : compositeFamily T M ⟶ T := Over.homMk M.hom rfl

instance compositeFamilyMap_mono [Mono M.hom] : Mono (compositeFamilyMap T M) := by
  have : Mono (compositeFamilyMap T M).left := inferInstanceAs (Mono M.hom)
  exact Over.mono_of_mono_left (compositeFamilyMap T M)

def familyLiftFactorizationEquiv {U : Over S} (j : U ⟶ T) :
    (Over.mk j.left ⟶ M) ≃ { v : U ⟶ compositeFamily T M // v ≫ compositeFamilyMap T M = j } where
  toFun p := ⟨Over.homMk p.left (by
    change p.left ≫ (M.hom ≫ T.hom) = U.hom
    rw [← Category.assoc, p.w]
    exact j.w), Over.OverMorphism.ext p.w⟩
  invFun v := Over.homMk v.val.left (congrArg Over.Hom.left v.property)
  left_inv p := Over.OverMorphism.ext rfl
  right_inv v := Subtype.ext (Over.OverMorphism.ext rfl)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FamilyLiftFactorization.Construction
