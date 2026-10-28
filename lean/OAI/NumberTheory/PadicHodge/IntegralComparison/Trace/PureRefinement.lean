import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureFunctorNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedPairingNaturality

/-! # Pure Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureRefinement

noncomputable section

/-! Pure Serre naturality descends through a common resolution before
any projective geometry is substituted. All maps are the original
dual-complex homology maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Map

variable {X : Scheme.{u}} (N : X.Modules)
  {P Q T : ChainComplex X.Modules ℕ} (a : P ⟶ Q) (b : P ⟶ T) (c : ℕ)
  [IsIso (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c)]

def map : (((Affine.LocalDualInvariance.functor N).obj (op T)).homology c) ⟶
    (((Affine.LocalDualInvariance.functor N).obj (op Q)).homology c) :=
  HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map b.op) c ≫
    inv (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c)

@[reassoc]
theorem map_left : PureRefinement.map N a b c ≫
    HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c =
      HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map b.op) c := by
  simp only [PureRefinement.map, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end Map

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (N : X.Modules) (τ : F.obj N ⟶ ModuleCat.of R R)
  {P Q T : ChainComplex X.Modules ℕ}
  [∀ q, ((InternalHomCechTotal.internalComplex N P.op).X q).IsQuasicoherent]
  [∀ q, ((InternalHomCechTotal.internalComplex N Q.op).X q).IsQuasicoherent]
  [∀ q, ((InternalHomCechTotal.internalComplex N T.op).X q).IsQuasicoherent]
  (hcover : iSup U = ⊤)
  (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
  (hPterms : InternalHomCechTotal.TermsAcyclic π U N P.op)
  (c : ℕ) (hPureP : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N P.op).ExactAt q)
  (hQ : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (Q.X i)))
  (hQterms : InternalHomCechTotal.TermsAcyclic π U N Q.op)
  (hPureQ : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N Q.op).ExactAt q)
  (hT : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (T.X i)))
  (hTterms : InternalHomCechTotal.TermsAcyclic π U N T.op)
  (hPureT : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N T.op).ExactAt q)
  (a : P ⟶ Q) (b : P ⟶ T)
  [IsIso (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c)]

include hP hPterms hPureP

@[reassoc]
theorem naturality (n : ℕ) {D₁ D₂ : ModuleCat.{u} R}
    (eP : (DualityHomology.coefficientComplex R F P).homology (n + c) ≅ D₁)
    (eQ : (DualityHomology.coefficientComplex R F Q).homology (n + c) ≅ D₁)
    (eT : (DualityHomology.coefficientComplex R F T).homology (n + c) ≅ D₂)
    (d : D₁ ⟶ D₂) (e : D₁ ⟶ D₁)
    (ha : HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F a)
      (n + c) ≫ eQ.hom = eP.hom ≫ e)
    (hb : HomologicalComplex.homologyMap (DualityHomologyNaturality.coefficientMap R F b)
      (n + c) ≫ eT.hom = eP.hom ≫ d)
    (he : e = 𝟙 D₁) :
    (PureFunctorNaturality.cohomologyFunctor π U n).map (PureRefinement.map N a b c) ≫
      (PureSerre.iso π U hU R F N τ Q hcover hQ hQterms c hPureQ n eQ).hom =
    (PureSerre.iso π U hU R F N τ T hcover hT hTterms c hPureT n eT).hom ≫
      DualTransportNaturality.dualMap R d := by
  apply RefinedPairingNaturality.of_factorization_identity
    (PureFunctorNaturality.cohomologyFunctor π U n)
    (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map a.op) c)
    (HomologicalComplex.homologyMap ((Affine.LocalDualInvariance.functor N).map b.op) c)
    (PureRefinement.map N a b c) (DualTransportNaturality.dualMap R d)
    (DualTransportNaturality.dualMap R e)
    (pL := PureSerre.iso π U hU R F N τ P hcover hP hPterms c hPureP n eP)
  · exact PureFunctorNaturality.naturality π U hU R F N τ hcover
      hP hPterms c hPureP hQ hQterms hPureQ a n eP eQ e ha
  · exact PureFunctorNaturality.naturality π U hU R F N τ hcover
      hP hPterms c hPureP hT hTterms hPureT b n eP eT d hb
  · subst e
    rfl
  · exact map_left N a b c

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureRefinement
