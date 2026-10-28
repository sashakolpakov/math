import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Unit Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.UnitRestrictions

noncomputable section

/-! Restriction of original regular units, including its exact
composition law on nested algebraic open subsets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (X : Scheme.{u})

def regularUnitRestrict {U V : X.Opens} (h : V ≤ U) : Γ(X, U)ˣ →* Γ(X, V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

theorem regularUnitRestrict_comp {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (a : Γ(X, U)ˣ) :
    regularUnitRestrict X k (regularUnitRestrict X h a) = regularUnitRestrict X (k.trans h) a := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE h).op (homOfLE k).op).symm a.val

theorem regularUnitRestrict_self {U : X.Opens} (a : Γ(X, U)ˣ) :
    regularUnitRestrict X le_rfl a = a := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (.op U)) a.val

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.UnitRestrictions
