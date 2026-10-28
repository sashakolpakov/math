import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitSection
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartScalars

/-! # Polynomial Section Map Defs -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionMapDefs

noncomputable section

/-! Actual homogeneous polynomial sections, normalized on a closed subscheme's affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Dimension

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction

universe u

local instance projectivePolynomialSectionMapDefsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectivePolynomialNativeUnitSectionsEquiv (j : σ) (n : ℕ) :
    homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n ≃ₗ[Γ(Spec (.of R), ⊤)]
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        (𝟙_ (Proj (homogeneousSubmodule σ R)).Modules ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) :=
  (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n).symm.trans
    (((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).mapIso
      (λ_ (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))).toLinearEquiv.symm)

def nativeUnitToPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟙_ Y.Modules ⟶ (Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) :=
  (TensorSections.monoidalUnitObjIso Y).hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

def closedProjectiveAmbientPolynomialSectionsMap {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n →ₗ[Γ(Spec (.of R), ⊤)]
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) ⊗
          TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) :=
  (((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).map
    (nativeUnitToPushforward f ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))).hom).comp
      (projectivePolynomialNativeUnitSectionsEquiv j n).toLinearMap

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionMapDefs
