import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureSerre
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopCechRightExact
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalDualInvariance

/-! # Pure Functor Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureFunctorNaturality

noncomputable section

/-! Pure Serre naturality expressed through the actual functor on
cohomology sheaves. This form composes with common refinements directly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

def cohomologyFunctor (n : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  TopCechRightExact.functor π U n ⋙ forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat

variable (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (N : X.Modules) (τ : F.obj N ⟶ ModuleCat.of R R)
  {P Q : ChainComplex X.Modules ℕ}
  [∀ q, ((InternalHomCechTotal.internalComplex N P.op).X q).IsQuasicoherent]
  [∀ q, ((InternalHomCechTotal.internalComplex N Q.op).X q).IsQuasicoherent]
  (hcover : iSup U = ⊤)
  (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
  (hPterms : InternalHomCechTotal.TermsAcyclic π U N P.op)
  (c : ℕ) (hPure : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N P.op).ExactAt q)
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
    (cohomologyFunctor π U n).map
        (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c) ≫
      (PureSerre.iso π U hU R F N τ P hcover hP hPterms c hPure n e₁).hom =
    (PureSerre.iso π U hU R F N τ Q hcover hQ hQterms c hPureQ n e₂).hom ≫
      DualTransportNaturality.dualMap R b := by
  exact PureSerre.naturality π U hU R F N τ hcover hP hPterms c hPure
    hQ hQterms hPureQ a n e₁ e₂ b he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureFunctorNaturality
