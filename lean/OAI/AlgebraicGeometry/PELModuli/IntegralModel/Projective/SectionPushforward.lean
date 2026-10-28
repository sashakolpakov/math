import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistProjectionFormula

/-! # Section Pushforward -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.SectionPushforward

noncomputable section

/-! Identify the sections of a twisted pushforward with the actual
sections of the induced projective twist on its source, over the base ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
universe u

def baseSectionsPushforwardEquiv {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules) :
    (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj ((Scheme.Modules.pushforward f).obj M) ≃ₗ[Γ(S, ⊤)]
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ π)).obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

attribute [local instance] MvPolynomial.gradedAlgebra
local instance c44ProjectiveSectionPushforwardMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def nativeProjectiveTwistSectionsEquiv {R : Type u} [CommRing R] {σ : Type} {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) (j : σ) (m : ℕ) :
    (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      (((Scheme.Modules.pushforward f).obj (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) ⊗
        SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ≃ₗ[Γ(Spec (.of R), ⊤)]
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        ((Scheme.Modules.pullback f).obj
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) := by
  let P := (Scheme.Modules.pullback f).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
  let e := (SheafCohomology.Projective.TwistProjectionFormula.MvPolynomial.coordinateHyperplanePoleSheafPowerPushforwardTensorIso f j m).app
    (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
  let eP : SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X ⊗ P ≅ P :=
    ((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl P) ≪≫ λ_ P
  exact ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).mapIso
    (e ≪≫ (Scheme.Modules.pushforward f).mapIso eP)).toLinearEquiv |>.trans
      (baseSectionsPushforwardEquiv f (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) P)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.SectionPushforward
