import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedSerreVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Closed Twist Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections

noncomputable section

open _root_.MvPolynomial

/-! Base-linear global sections of projective twists under a closed immersion. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace MonoidalCategory
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance closedTwistSectionsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def closedImmersion_projectiveTwist_sectionsLinearEquiv {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (M : X.Modules) (j : σ) (n : ℕ) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      (M ⊗ (Scheme.Modules.pullback f).obj (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))
      ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((Scheme.Modules.pushforward f).obj M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) := by
  let N := (Scheme.Modules.pushforward f).obj M
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let T : X.Modules := M ⊗ (Scheme.Modules.pullback f).obj P
  let U := StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)
  have hU : IsOpenCover U := IsOpenCover.mk (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  let ePF : N ⊗ P ≅ (Scheme.Modules.pushforward f).obj T :=
    (TwistProjectionFormula.MvPolynomial.coordinateHyperplanePoleSheafPowerPushforwardTensorIso f j n).app M
  let F := OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) U
  let eC := OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) T U ≪≫ (F.mapIso ePF).symm
  exact (BaseZeroSections.orderedBaseCechHZeroGlobalSectionsLinearEquiv
    (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) T (fun k => f ⁻¹ᵁ U k)
    (hU.comap f.base.hom)).symm.trans
      ((HomologicalComplex.homologyMapIso eC 0).toLinearEquiv.trans
        (BaseZeroSections.orderedBaseCechHZeroGlobalSectionsLinearEquiv
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (N ⊗ P) U hU))

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections
