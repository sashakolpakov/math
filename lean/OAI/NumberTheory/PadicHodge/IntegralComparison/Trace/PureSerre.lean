import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotalNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomConcentrationNaturality

/-! # Pure Serre -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureSerre

noncomputable section

/-! Combine trace duality and concentration before specializing to a
geometric resolution. Both the pure Serre isomorphism and its naturality
then use the same actual total-complex comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (N : X.Modules) (τ : F.obj N ⟶ ModuleCat.of R R)
  (P : ChainComplex X.Modules ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex N P.op).X q).IsQuasicoherent]
  (hcover : iSup U = ⊤)
  (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
  (hPterms : InternalHomCechTotal.TermsAcyclic π U N P.op)
  (c : ℕ) (hPure : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N P.op).ExactAt q)

def iso (n : ℕ) {D : ModuleCat.{u} R}
    (e : (DualityHomology.coefficientComplex R F P).homology (n + c) ≅ D) :=
  ConcentratedSerre.Comparison.iso π U hU N P.op c hPure n
    (SerreTotal.iso π U R F N τ P hcover hP hPterms (n + c) e)

variable {P}
  {Q : ChainComplex X.Modules ℕ}
  [∀ q, ((InternalHomCechTotal.internalComplex N Q.op).X q).IsQuasicoherent]
  (hQ : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (Q.X i)))
  (hQterms : InternalHomCechTotal.TermsAcyclic π U N Q.op)
  (hPureQ : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N Q.op).ExactAt q)
  (a : P ⟶ Q)

@[reassoc]
theorem naturality (n : ℕ) {D₁ D₂ : ModuleCat.{u} R}
    (e₁ : (DualityHomology.coefficientComplex R F P).homology (n + c) ≅ D₁)
    (e₂ : (DualityHomology.coefficientComplex R F Q).homology (n + c) ≅ D₂)
    (b : D₁ ⟶ D₂)
    (he : HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F a)
      (n + c) ≫ e₂.hom = e₁.hom ≫ b) :
    InternalHomConcentrationNaturality.cohomologyMap π U N c
      (SerreTotalNaturality.oppositeMap a) n ≫
        (iso π U hU R F N τ P hcover hP hPterms c hPure n e₁).hom =
      (iso π U hU R F N τ Q hcover hQ hQterms c hPureQ n e₂).hom ≫
        DualTransportNaturality.dualMap R b := by
  exact InternalHomConcentrationNaturality.serre_naturality π U hU N c hPureQ hPure
    (SerreTotalNaturality.oppositeMap a) n
    (SerreTotal.iso π U R F N τ Q hcover hQ hQterms (n + c) e₂)
    (SerreTotal.iso π U R F N τ P hcover hP hPterms (n + c) e₁)
    (DualTransportNaturality.dualMap R b)
    (SerreTotalNaturality.naturality π U R F N τ a hcover hP hQ hPterms hQterms
      (n + c) e₁ e₂ b he)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureSerre
