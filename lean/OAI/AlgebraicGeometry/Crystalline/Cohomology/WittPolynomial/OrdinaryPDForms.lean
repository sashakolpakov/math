import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.BasePowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeOrdinaryPDForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq

/-! # Ordinary PD Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.OrdinaryPDForms.WittPolynomialOrdinaryPDForms

noncomputable section

/-! # Actual ordinary and base-PD polynomial de Rham complexes agree integrally -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W

def basis (n : ℕ) : Module.Basis (Set.powersetCard σ n) P (DeRhamPresentationTo.DeRhamPresentation.Form W P n) :=
  (PD.FormsTensor.PDFormsTensor.tensorBasis W P σ n).map (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.formsEquiv W σ n)

instance forms_torsionFree (n : ℕ) : Module.IsTorsionFree P (DeRhamPresentationTo.DeRhamPresentation.Form W P n) :=
  (basis p k σ n).isTorsionFree

def complexIso : DeRhamPresentationTo.DeRhamPresentation.complex W P ≅
    PD.DeRham.PDDeRham.complex W P (BasePowers.WittPolynomialBasePowers.ideal p k σ) (BasePowers.WittPolynomialBasePowers.dividedPowers p k σ) :=
  FreeOrdinaryPDForms.TorsionFreeOrdinaryPDForms.complexIso W P (BasePowers.WittPolynomialBasePowers.ideal p k σ)
    (BasePowers.WittPolynomialBasePowers.dividedPowers p k σ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.OrdinaryPDForms.WittPolynomialOrdinaryPDForms
