import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.UnitRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionNaturality

/-! # Unit Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitCoordinates

noncomputable section

/-! Units on an open subscheme and ambient regular units agree through
the actual top-section isomorphism, including restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}}

def openUnitToRegular (U : X.Opens) : Γ(U.toScheme, ⊤)ˣ →* Γ(X, U)ˣ :=
  Units.map U.topIso.hom.hom.toMonoidHom

def regularUnitToOpen (U : X.Opens) : Γ(X, U)ˣ →* Γ(U.toScheme, ⊤)ˣ :=
  Units.map U.topIso.inv.hom.toMonoidHom

theorem openUnitToRegular_toOpen (U : X.Opens) (a : Γ(X, U)ˣ) :
    openUnitToRegular U (regularUnitToOpen U a) = a := by
  apply Units.ext
  exact U.topIso.inv_hom_id_apply a.val

theorem regularUnitToOpen_toRegular (U : X.Opens) (a : Γ(U.toScheme, ⊤)ˣ) :
    regularUnitToOpen U (openUnitToRegular U a) = a := by
  apply Units.ext
  exact U.topIso.hom_inv_id_apply a.val

theorem openUnitToRegular_injective (U : X.Opens) : Function.Injective (openUnitToRegular U) := by
  intro a b h
  exact (regularUnitToOpen_toRegular U a).symm.trans
    ((congrArg (regularUnitToOpen U) h).trans (regularUnitToOpen_toRegular U b))

theorem openUnitToRegular_restrict {U V : X.Opens} (h : V ≤ U) (a : Γ(U.toScheme, ⊤)ˣ) :
    openUnitToRegular V (Units.map (X.homOfLE h).appTop.hom.toMonoidHom a) =
      Regular.UnitRestrictions.regularUnitRestrict X h (openUnitToRegular U a) := by
  apply Units.ext
  exact TopSectionNaturality.openTopSection_restrict h a.val

theorem openUnitToRegular_resLE {Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (a : Γ(U.toScheme, ⊤)ˣ) :
    openUnitToRegular V (Units.map (f.resLE U V h).appTop.hom.toMonoidHom a) =
      Units.map (f.appLE U V h).hom.toMonoidHom (openUnitToRegular U a) := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (arrowResLEAppIso f U V h).hom.w.symm a.val

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitCoordinates
