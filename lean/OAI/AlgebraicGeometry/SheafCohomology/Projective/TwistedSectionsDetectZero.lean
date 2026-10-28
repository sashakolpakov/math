import OAI.AlgebraicGeometry.SheafCohomology.Projective.BoundedNegativeQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitHomTopSections

/-! # Twisted Sections Detect Zero -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectZero

noncomputable section

open _root_.MvPolynomial

/-! Sufficiently positive sections detect zero coherent projective modules. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitHomTopSections
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance twistedDetectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

def coordinateNegativeTwistHomEquivTwistedSections (j : σ) (n : ℕ)
    (M : (Proj (homogeneousSubmodule σ R)).Modules) :
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ⟶ M) ≃
      Γ(M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤) := by
  let X := Proj (homogeneousSubmodule σ R)
  let N := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let E := PairedTwistEquivalence.MvPolynomial.coordinateHyperplaneTwistPairEquivalence (R := R) j n
  let e₀ : (N ⟶ M) ≃ (N ⊗ P ⟶ M ⊗ P) := E.fullyFaithfulFunctor.homEquiv
  let e₁ : (N ⊗ P ⟶ M ⊗ P) ≃ (Invertible.Scheme.Modules.unitObj X ⟶ M ⊗ P) :=
    Iso.homCongr (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n ≪≫
      TensorSections.monoidalUnitObjIso X) (Iso.refl _)
  exact e₀.trans (e₁.trans (UnitHomTopSections.unitHomTopSectionsEquiv (M ⊗ P)))

theorem finiteType_isZero_of_eventually_twistedSections_subsingleton [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (b : ℕ)
    (hb : ∀ n : ℕ, b ≤ n → Subsingleton Γ(M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤)) :
    IsZero M := by
  obtain ⟨s, d, f, hd, hf⟩ := BoundedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient_above M j b
  let := hf
  apply IsZero.of_epi_eq_zero f
  apply Sigma.hom_ext
  intro k
  have := hb (d k) (hd k)
  have : Subsingleton (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k) ⟶ M) :=
    (coordinateNegativeTwistHomEquivTwistedSections j (d k) M).injective.subsingleton
  exact Subsingleton.elim _ _

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectZero
