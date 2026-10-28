import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureUnitNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedTraceNaturality

/-! # Pure Unit Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureUnitRefinement

noncomputable section

/-! Evaluation at a preserved degree-zero class descends through a
common resolution. The three coefficient complexes may have distinct
cohomology objects; their actual maps carry the chosen classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (N : X.Modules) (τ : F.obj N ⟶ ModuleCat.of R R)
  {P Q T : ChainComplex X.Modules ℕ}
  [∀ q, ((InternalHomCechTotal.internalComplex N P.op).X q).IsQuasicoherent]
  [∀ q, ((InternalHomCechTotal.internalComplex N Q.op).X q).IsQuasicoherent]
  [∀ q, ((InternalHomCechTotal.internalComplex N T.op).X q).IsQuasicoherent]
  (hcover : iSup U = ⊤)
  (hP : ∀ j, Function.Bijective (DualityDescent.pairingMap F τ (P.X j)))
  (hPterms : InternalHomCechTotal.TermsAcyclic π U N P.op)
  (c : ℕ) (hPureP : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N P.op).ExactAt q)
  (hQ : ∀ j, Function.Bijective (DualityDescent.pairingMap F τ (Q.X j)))
  (hQterms : InternalHomCechTotal.TermsAcyclic π U N Q.op)
  (hPureQ : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N Q.op).ExactAt q)
  (hT : ∀ j, Function.Bijective (DualityDescent.pairingMap F τ (T.X j)))
  (hTterms : InternalHomCechTotal.TermsAcyclic π U N T.op)
  (hPureT : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N T.op).ExactAt q)
  (a : P ⟶ Q) (b : P ⟶ T)
  [IsIso (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c)]

include hP hPterms hPureP

theorem naturality (i k : ℕ) (VP VQ VT : ℕ → ModuleCat.{u} R)
    (eP : (DualityHomology.coefficientComplex R F P).homology (i + c) ≅ VP k)
    (eQ : (DualityHomology.coefficientComplex R F Q).homology (i + c) ≅ VQ k)
    (eT : (DualityHomology.coefficientComplex R F T).homology (i + c) ≅ VT k)
    (hk : k = 0) (da : ∀ j, VP j ⟶ VQ j) (db : ∀ j, VP j ⟶ VT j)
    (heA : HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F a)
      (i + c) ≫ eQ.hom = eP.hom ≫ da k)
    (heB : HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F b)
      (i + c) ≫ eT.hom = eP.hom ≫ db k)
    (vP : VP 0) (vQ : VQ 0) (vT : VT 0) (ha : da 0 vP = vQ) (hb : db 0 vP = vT) :
    (PureFunctorNaturality.cohomologyFunctor π U i).map
        (PureRefinement.map N a b c) ≫
      PureUnitNaturality.trace π U hU R F N τ Q hcover hQ hQterms c hPureQ i k VQ eQ hk vQ =
    PureUnitNaturality.trace π U hU R F N τ T hcover hT hTterms c hPureT i k VT eT hk vT := by
  exact RefinedTraceNaturality.of_factorization
    (PureFunctorNaturality.cohomologyFunctor π U i)
    (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c)
    (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map b.op) c)
    (PureRefinement.map N a b c)
    (PureUnitNaturality.trace π U hU R F N τ Q hcover hQ hQterms c hPureQ i k VQ eQ hk vQ)
    (PureUnitNaturality.trace π U hU R F N τ T hcover hT hTterms c hPureT i k VT eT hk vT)
    (PureUnitNaturality.trace π U hU R F N τ P hcover hP hPterms c hPureP i k VP eP hk vP)
    (PureUnitNaturality.naturality π U hU R F N τ hcover hP hPterms c hPureP
      hQ hQterms hPureQ a i k VP VQ eP eQ hk da heA vP vQ ha)
    (PureUnitNaturality.naturality π U hU R F N τ hcover hP hPterms c hPureP
      hT hTterms hPureT b i k VP VT eP eT hk db heB vP vT hb)
    (PureRefinement.map_left N a b c)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureUnitRefinement
