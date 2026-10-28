import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureFunctorNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedSerreTraceNaturality

/-! # Pure Unit Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureUnitNaturality

noncomputable section

/-! Evaluation at degree zero is combined with pure Serre naturality
before specializing any of the geometric resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (N : X.Modules) (τ : F.obj N ⟶ ModuleCat.of R R)
  (P : ChainComplex X.Modules ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex N P.op).X q).IsQuasicoherent]
  (hcover : iSup U = ⊤)
  (hP : ∀ j, Function.Bijective (DualityDescent.pairingMap F τ (P.X j)))
  (hPterms : InternalHomCechTotal.TermsAcyclic π U N P.op)
  (c : ℕ) (hPureP : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N P.op).ExactAt q)

def pairing (i k : ℕ) (V : ℕ → ModuleCat.{u} R)
    (e : (DualityHomology.coefficientComplex R F P).homology (i + c) ≅ V k) (hk : k = 0) :=
  IndexedSerreUnitTrace.pairing R V
    (PureSerre.iso π U hU R F N τ P hcover hP hPterms c hPureP i e) hk

def trace (i k : ℕ) (V : ℕ → ModuleCat.{u} R)
    (e : (DualityHomology.coefficientComplex R F P).homology (i + c) ≅ V k)
    (hk : k = 0) (v : V 0) :=
  SerreUnitTrace.trace R (pairing π U hU R F N τ P hcover hP hPterms c hPureP i k V e hk) v

variable {P}
  {Q : ChainComplex X.Modules ℕ}
  [∀ q, ((InternalHomCechTotal.internalComplex N Q.op).X q).IsQuasicoherent]
  (hQ : ∀ j, Function.Bijective (DualityDescent.pairingMap F τ (Q.X j)))
  (hQterms : InternalHomCechTotal.TermsAcyclic π U N Q.op)
  (hPureQ : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N Q.op).ExactAt q)
  (a : P ⟶ Q)

theorem naturality (i k : ℕ) (V₁ V₂ : ℕ → ModuleCat.{u} R)
    (e₁ : (DualityHomology.coefficientComplex R F P).homology (i + c) ≅ V₁ k)
    (e₂ : (DualityHomology.coefficientComplex R F Q).homology (i + c) ≅ V₂ k)
    (hk : k = 0) (b : ∀ j, V₁ j ⟶ V₂ j)
    (he : HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F a)
      (i + c) ≫ e₂.hom = e₁.hom ≫ b k)
    (v₁ : V₁ 0) (v₂ : V₂ 0) (hv : b 0 v₁ = v₂) :
    (PureFunctorNaturality.cohomologyFunctor π U i).map
        (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c) ≫
      trace π U hU R F N τ P hcover hP hPterms c hPureP i k V₁ e₁ hk v₁ =
    trace π U hU R F N τ Q hcover hQ hQterms c hPureQ i k V₂ e₂ hk v₂ :=
  IndexedSerreTraceNaturality.trace R V₁ V₂
    (PureSerre.iso π U hU R F N τ P hcover hP hPterms c hPureP i e₁)
    (PureSerre.iso π U hU R F N τ Q hcover hQ hQterms c hPureQ i e₂)
    hk _ b (PureFunctorNaturality.naturality π U hU R F N τ hcover hP hPterms c hPureP
      hQ hQterms hPureQ a i e₁ e₂ (b k) he) v₁ v₂ hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureUnitNaturality
