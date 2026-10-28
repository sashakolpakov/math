import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantTransport
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CoefficientCoherence
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport

/-! # Cohomology Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CohomologyCoherence

noncomputable section

/-!
# Functoriality of actual rational pro-étale cohomology

The Ext-defined cohomological transport satisfies identity and composition.
These laws use the canonical constant and continuous coefficient sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.ProEtaleCoherence
  ConstantTransport CoefficientCoherence ExtTransport

variable (p : ℕ) [Fact p.Prime]
variable {X Y Z : Scheme.{u}}

theorem cohomologyTransport_refl (X : Scheme.{u}) (n : ℕ) :
    IntegralComparison.Etale.Frobenius.cohomologyTransport p (Iso.refl X) n = LinearEquiv.refl _ _ := by
  have ha : IntegralComparison.Etale.Frobenius.constantUnitTransport p (Iso.refl X) =
      (ProEtaleCoherence.proEtaleSheafCongr_refl (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) X).app
        (IntegralComparison.Cohomology.constantUnitSheaf p X) := by
    apply Iso.ext
    exact (ConstantTransport.constantTransport_refl (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) X
      (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))).symm
  have hb : IntegralComparison.Etale.Frobenius.coefficientSheafTransport p (Iso.refl X) =
      (ProEtaleCoherence.proEtaleSheafCongr_refl (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) X).app
        (IntegralComparison.Cohomology.rationalCoefficientSheaf p X) := by
    apply Iso.ext
    exact (CoefficientCoherence.coefficientTransport_refl p X).symm
  ext α
  change CategoryTheory.Abelian.Ext (IntegralComparison.Cohomology.constantUnitSheaf p X) (IntegralComparison.Cohomology.rationalCoefficientSheaf p X) n at α
  change ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p)
    (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (Iso.refl X)).functor
    (IntegralComparison.Etale.Frobenius.constantUnitTransport p (Iso.refl X)) (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p (Iso.refl X)) n α = α
  rw [ha, hb]
  have h := ExtTransport.exactTransport_natIso (IntegralComparison.Cohomology.Coeff.{u} p)
    (ProEtaleCoherence.proEtaleSheafCongr_refl (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) X)
    (Iso.refl (IntegralComparison.Cohomology.constantUnitSheaf p X)) (Iso.refl (IntegralComparison.Cohomology.rationalCoefficientSheaf p X)) α
  have ht := congrArg₂ (fun iA iB => ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p)
    (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (Iso.refl X)).functor iA iB n α)
    (Iso.trans_refl ((ProEtaleCoherence.proEtaleSheafCongr_refl (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) X).app
      (IntegralComparison.Cohomology.constantUnitSheaf p X))).symm
    (Iso.trans_refl ((ProEtaleCoherence.proEtaleSheafCongr_refl (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) X).app
      (IntegralComparison.Cohomology.rationalCoefficientSheaf p X))).symm
  exact ht.trans (h.trans (ExtTransport.exactTransport_id (IntegralComparison.Cohomology.Coeff.{u} p) α))

theorem cohomologyTransport_comp (e : X ≅ Y) (f : Y ≅ Z) (n : ℕ) :
    (IntegralComparison.Etale.Frobenius.cohomologyTransport p e n).trans (IntegralComparison.Etale.Frobenius.cohomologyTransport p f n) =
      IntegralComparison.Etale.Frobenius.cohomologyTransport p (e ≪≫ f) n := by
  have ha : (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) f).functor.mapIso
        (IntegralComparison.Etale.Frobenius.constantUnitTransport p e) ≪≫ IntegralComparison.Etale.Frobenius.constantUnitTransport p f =
      (ProEtaleCoherence.proEtaleSheafCongr_comp (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e f).app
        (IntegralComparison.Cohomology.constantUnitSheaf p X) ≪≫ IntegralComparison.Etale.Frobenius.constantUnitTransport p (e ≪≫ f) := by
    apply Iso.ext
    exact ConstantTransport.constantTransport_comp (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e f
      (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))
  have hb : (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) f).functor.mapIso
        (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p e) ≪≫ IntegralComparison.Etale.Frobenius.coefficientSheafTransport p f =
      (ProEtaleCoherence.proEtaleSheafCongr_comp (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e f).app
        (IntegralComparison.Cohomology.rationalCoefficientSheaf p X) ≪≫ IntegralComparison.Etale.Frobenius.coefficientSheafTransport p (e ≪≫ f) := by
    apply Iso.ext
    exact CoefficientCoherence.coefficientTransport_comp p e f
  ext α
  change CategoryTheory.Abelian.Ext (IntegralComparison.Cohomology.constantUnitSheaf p X) (IntegralComparison.Cohomology.rationalCoefficientSheaf p X) n at α
  change ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p)
    (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) f).functor
    (IntegralComparison.Etale.Frobenius.constantUnitTransport p f) (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p f) n
    (ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p)
      (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e).functor
      (IntegralComparison.Etale.Frobenius.constantUnitTransport p e) (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p e) n α) =
    ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p)
      (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (e ≪≫ f)).functor
      (IntegralComparison.Etale.Frobenius.constantUnitTransport p (e ≪≫ f)) (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p (e ≪≫ f)) n α
  rw [ExtTransport.exactTransport_comp, ha, hb]
  exact ExtTransport.exactTransport_natIso (IntegralComparison.Cohomology.Coeff.{u} p)
    (ProEtaleCoherence.proEtaleSheafCongr_comp (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e f)
    (IntegralComparison.Etale.Frobenius.constantUnitTransport p (e ≪≫ f)) (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p (e ≪≫ f)) α

theorem cohomologyPullback_refl (X : Scheme.{u}) (n : ℕ) :
    IntegralComparison.Etale.Frobenius.cohomologyPullback p (Iso.refl X) n = LinearEquiv.refl _ _ :=
  cohomologyTransport_refl p X n

theorem cohomologyPullback_comp (e : X ≅ Y) (f : Y ≅ Z) (n : ℕ) :
    (IntegralComparison.Etale.Frobenius.cohomologyPullback p f n).trans (IntegralComparison.Etale.Frobenius.cohomologyPullback p e n) =
      IntegralComparison.Etale.Frobenius.cohomologyPullback p (e ≪≫ f) n :=
  cohomologyTransport_comp p f.symm e.symm n

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CohomologyCoherence
