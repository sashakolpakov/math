import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomologyNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualTransportNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

/-! # Serre Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotalNaturality

noncomputable section

/-! The trace duality on the actual Čech total is natural under maps
of the original resolutions and their complementary cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (N : X.Modules) (τ : F.obj N ⟶ ModuleCat.of R R)
  {P Q : ChainComplex X.Modules ℕ} (a : P ⟶ Q)

def oppositeMap : Q.op ⟶ P.op :=
  (HomologicalComplex.opFunctor X.Modules (.down ℕ)).map a.op

@[reassoc]
theorem naturality (hU : iSup U = ⊤)
    (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
    (hQ : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (Q.X i)))
    (hPterms : InternalHomCechTotal.TermsAcyclic π U N P.op)
    (hQterms : InternalHomCechTotal.TermsAcyclic π U N Q.op)
    (n : ℕ) {D₁ D₂ : ModuleCat.{u} R}
    (e₁ : (DualityHomology.coefficientComplex R F P).homology n ≅ D₁)
    (e₂ : (DualityHomology.coefficientComplex R F Q).homology n ≅ D₂)
    (b : D₁ ⟶ D₂)
    (he : HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F a) n ≫ e₂.hom =
      e₁.hom ≫ b) :
    HomologicalComplex.homologyMap (InternalHomTotalNaturality.totalMap π U N (oppositeMap a)) n ≫
        (SerreTotal.iso π U R F N τ P hU hP hPterms n e₁).hom =
      (SerreTotal.iso π U R F N τ Q hU hQ hQterms n e₂).hom ≫
        DualTransportNaturality.dualMap R b := by
  have htrace := DualTransportNaturality.transport_naturality R
    (HomologicalComplex.homologyMap (DualityHomologyNaturality.homMap (ω := N) a) n)
    (HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F a) n) b
    (DualityHomology.homologyIso R F τ P hP n)
    (DualityHomology.homologyIso R F τ Q hQ n) e₁ e₂
    (DualityHomologyNaturality.naturality R F τ a hP hQ n) he
  have hc := InternalHomTotalNaturality.homology_naturality π U N (oppositeMap a)
    hU hQterms hPterms n
  have hci := CohomologyConcentrationNaturality.inverse_square _ _
    (InternalHomCechTotal.homologyIso π U N Q.op hU hQterms n)
    (InternalHomCechTotal.homologyIso π U N P.op hU hPterms n) hc
  simpa only [SerreTotal.iso, InternalHomTotalTransport.transport,
    InternalHomCechTotal.comparison, DualityHomology.homologyIsoTo,
    Iso.trans_hom, Iso.symm_hom, Category.assoc] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hci htrace

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotalNaturality
