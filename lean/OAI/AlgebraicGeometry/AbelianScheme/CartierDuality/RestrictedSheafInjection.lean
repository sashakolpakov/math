import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Restricted Sheaf Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RestrictedSheafInjection.Construction.Schemes

noncomputable section

/-! Injectivity after restricting actual fppf sheaves and sheafifying the target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- An injective restricted map from an actual sheaf remains injective after target sheafification. -/
theorem restricted_sheafification_injective
    {S T : Scheme.{u}} (s : T ⟶ S)
    (X : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) (a : X.obj ⟶ F)
    (ha : ∀ Q : Over T, Function.Injective (a.app (.op ((Over.map s).obj Q))))
    (Q : Over T) :
    Function.Injective ((a ≫ toSheafify (Scheme.fppfTopology.over S) F).app
      (.op ((Over.map s).obj Q))) := by
  let J := Scheme.fppfTopology.over T
  let K := Scheme.fppfTopology.over S
  let X' := (Scheme.fppfTopology.overMapPullback (Type (u + 1)) s).obj X
  let a' : X'.obj ⟶ (Over.map s).op ⋙ F := Functor.whiskerLeft (Over.map s).op a
  have : Presheaf.IsLocallyInjective J a' :=
    Presheaf.isLocallyInjective_of_injective J a' (fun V => ha V.unop)
  let b : X' ⟶ (presheafToSheaf J (Type (u + 1))).obj ((Over.map s).op ⋙ F) :=
    ⟨a' ≫ toSheafify J ((Over.map s).op ⋙ F)⟩
  have : Sheaf.IsLocallyInjective b := inferInstanceAs
    (Presheaf.IsLocallyInjective J (a' ≫ toSheafify J ((Over.map s).op ⋙ F)))
  have hb := (Sheaf.isLocallyInjective_iff_injective b).mp inferInstance (.op Q)
  let e := ((Over.map s).pushforwardContinuousSheafificationCompatibility (Type (u + 1)) J K).app F
  have he := NatTrans.congr_app
    ((Over.map s).toSheafify_pullbackSheafificationCompatibility (Type (u + 1)) J K F) (.op Q)
  intro x y h
  apply hb
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (.op Q))).injective
  exact (ConcreteCategory.congr_hom he (a.app (.op ((Over.map s).obj Q)) x)).trans
    (h.trans (ConcreteCategory.congr_hom he (a.app (.op ((Over.map s).obj Q)) y)).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RestrictedSheafInjection.Construction.Schemes
