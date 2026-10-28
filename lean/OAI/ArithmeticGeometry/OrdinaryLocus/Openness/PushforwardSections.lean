import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleProjectionFormula
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Pushforward Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardSections.Construction

noncomputable section

/-! The projection formula on actual base-linear global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

universe u

def baseGlobalSectionsPushforwardEquiv {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules) :
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor g).obj ((Scheme.Modules.pushforward f).obj M) ≃ₗ[Γ(S, ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ g)).obj M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineBundleProjectionSectionsEquiv {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (M : X.Modules) :
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor g).obj
      (SheafTensor.Construction.sheafTensor ((Scheme.Modules.pushforward f).obj M) L.sheaf) ≃ₗ[Γ(S, ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ g)).obj
        (SheafTensor.Construction.sheafTensor M ((Scheme.Modules.pullback f).obj L.sheaf)) :=
  ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor g).mapIso (LineBundleProjectionFormula.Construction.lineBundleProjectionFormula f L M)).toLinearEquiv.trans
    (baseGlobalSectionsPushforwardEquiv f g _)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardSections.Construction
