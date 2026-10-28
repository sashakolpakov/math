import OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialDP
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare

/-! # Shifted Polynomial Complex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialComplex.ShiftedPolynomialPoincare

noncomputable section

/-!
# Relative PD Poincaré around arbitrary chosen coordinate lifts

The actual PD envelope of coordinate differences is identified with the
relative free PD algebra. Its actual relative differential-form complex
therefore contracts onto the coefficient ring, including for torsion
PD bases.
-/

open _root_.CategoryTheory

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I) (x : σ → R) [Fintype σ]

local notation "P" => MvPolynomial σ R
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ J
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ J
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ J
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ

attribute [local instance] ShiftedPolynomialDP.ShiftedPolynomialEnvelope.envelopeBaseAlgebra

def complexIso : PD.DeRham.PDDeRham.complex R E IE ε ≅ PD.DeRham.PDDeRham.complex R G IG γ :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.complexIso (A := CommAlgCat.of R E) (B := CommAlgCat.of R G)
    (ShiftedPolynomialDP.ShiftedPolynomialEnvelope.algebraEquiv R σ I δ x)
    (ShiftedPolynomialDP.ShiftedPolynomialEnvelope.algebraEquiv_isDPMorphism R σ I δ x)
    (ShiftedPolynomialDP.ShiftedPolynomialEnvelope.algebraEquiv_symm_isDPMorphism R σ I δ x)

/-- The actual relative PD differential forms of the shifted polynomial envelope contract. -/
def homotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) (PD.DeRham.PDDeRham.complex R E IE ε) :=
  (FreeRelative.Poincare.FreeRelativePoincare.homotopyEquiv R σ I δ).trans
    (HomotopyEquiv.ofIso (complexIso R σ I δ x).symm)

def augmentation : (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R) ⟶
    PD.DeRham.PDDeRham.complex R E IE ε := (homotopyEquiv R σ I δ x).hom

instance augmentation_quasiIso : QuasiIso (augmentation R σ I δ x) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv R σ I δ x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialComplex.ShiftedPolynomialPoincare
