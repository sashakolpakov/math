import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.RestrictionSurjective
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.SectionPushforward
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials

/-! # Polynomial Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PolynomialRestriction

noncomputable section

/-! The actual restriction of homogeneous polynomials to the induced
projective twist on a closed subscheme is eventually surjective. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) (j : σ) (m : ℕ)
local instance c44ProjectivePolynomialRestrictionMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory Y

def nativeTwistSectionRestriction :
    (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) →ₗ[Γ(Spec (.of R), ⊤)]
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        ((Scheme.Modules.pullback f).obj
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) := by
  let Y := Proj (MvPolynomial.homogeneousSubmodule σ R)
  let H := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m
  let G := SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let e : SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y ⊗ H ≅ H :=
    ((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).symm ⊗ᵢ Iso.refl H) ≪≫ λ_ H
  let q := (SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j m).functor.map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  exact (SectionPushforward.PolarizationEmbedding.nativeProjectiveTwistSectionsEquiv f j m).toLinearMap.comp
    ((G.map q).hom.comp (G.mapIso e).inv.hom)

theorem nativeTwistSectionRestriction_surjective
    (h : Function.Surjective
      (((SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j m).functor.map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).app ⊤)) :
    Function.Surjective (nativeTwistSectionRestriction f j m) := by
  exact (SectionPushforward.PolarizationEmbedding.nativeProjectiveTwistSectionsEquiv f j m).surjective.comp
    (h.comp (ConcreteCategory.bijective_of_isIso _).surjective)

variable [Fintype σ] [LinearOrder σ]

def nativePolynomialRestriction :
    MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤) m →ₗ[Γ(Spec (.of R), ⊤)]
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        ((Scheme.Modules.pullback f).obj
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) := by
  letI := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
  exact (nativeTwistSectionRestriction f j m).comp
    (SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m).symm.toLinearMap

omit m in
theorem eventually_nativePolynomialRestriction_surjective [IsNoetherianRing R] [IsClosedImmersion f] :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m → Function.Surjective (nativePolynomialRestriction f j m) := by
  obtain ⟨b, hb⟩ := RestrictionSurjective.PolarizationEmbedding.eventually_projective_restriction_surjective f j
  refine ⟨b, fun m hm => ?_⟩
  let := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
  exact (nativeTwistSectionRestriction_surjective f j m (hb m hm)).comp
    (SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m).symm.surjective

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PolynomialRestriction
