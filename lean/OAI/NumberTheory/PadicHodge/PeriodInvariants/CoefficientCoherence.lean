import OAI.NumberTheory.PadicHodge.PeriodInvariants.ProEtaleCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Coefficient Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CoefficientCoherence

noncomputable section

/-!
# Coherence of the actual rational coefficient sheaf

Transport of the pro-étale site preserves underlying schemes. Hence the sheaf
of continuous p-adic-valued functions has compatible identity and composition
identifications under transport.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.ProEtaleCoherence

variable (p : ℕ) [Fact p.Prime]
variable {X Y Z : Scheme.{u}}

theorem coefficientTransport_refl (X : Scheme.{u}) :
    (ProEtaleCoherence.proEtaleSheafCongr_refl (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) X).hom.app
        (IntegralComparison.Cohomology.rationalCoefficientSheaf p X) =
      (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p (Iso.refl X)).hom := by
  ext U a
  rfl

theorem coefficientTransport_comp (e : X ≅ Y) (f : Y ≅ Z) :
    (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) f).functor.map
        (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p e).hom ≫ (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p f).hom =
      (ProEtaleCoherence.proEtaleSheafCongr_comp (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e f).hom.app
        (IntegralComparison.Cohomology.rationalCoefficientSheaf p X) ≫ (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p (e ≪≫ f)).hom := by
  ext U a
  rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CoefficientCoherence
