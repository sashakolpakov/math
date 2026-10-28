import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureSerre
import OAI.NumberTheory.PadicHodge.IntegralComparison.SerreUnitTrace

/-! # Mixed Pure Serre Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureSerreMap

noncomputable section

/-! Actual total dual maps between sheaves of different codimensions
induce the mixed-degree Serre map. This includes the point-class map
from a point's degree-zero dualizing cohomology to top forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
  (N : X.Modules) (P : ChainComplex X.Modules ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex N P.op).X q).IsQuasicoherent]
  (c : ℕ) (hPure : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N P.op).ExactAt q)

def concentration (i d : ℕ) (hi : d = i + c) :
    (InternalHomCechTotal.additiveTotal π U N P.op).homology d ≅
      (forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat).obj
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π
          ((InternalHomCechTotal.internalComplex N P.op).homology c) U).homology i) :=
  eqToIso (congrArg (fun k => (InternalHomCechTotal.additiveTotal π U N P.op).homology k) hi) ≪≫
    InternalHomCechConcentration.totalHomologyIso π U hU N P.op c hPure i

variable (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (τ : F.obj N ⟶ ModuleCat.of R R) (hcover : iSup U = ⊤)
  (hP : ∀ q, Function.Bijective (Trace.DualityDescent.pairingMap F τ (P.X q)))
  (hPterms : InternalHomCechTotal.TermsAcyclic π U N P.op)

def pairing (i d : ℕ) (hi : d = i + c) {D : ModuleCat.{u} R}
    (e : (Trace.DualityHomology.coefficientComplex R F P).homology d ≅ D) :=
  (concentration π U hU N P c hPure i d hi).symm ≪≫
    Trace.SerreTotal.iso π U R F N τ P hcover hP hPterms d e

variable {P} {Q : ChainComplex X.Modules ℕ}
  [∀ q, ((InternalHomCechTotal.internalComplex N Q.op).X q).IsQuasicoherent]
  (c' : ℕ) (hPureQ : ∀ q, q ≠ c' → (InternalHomCechTotal.internalComplex N Q.op).ExactAt q)
  (hQ : ∀ q, Function.Bijective (Trace.DualityDescent.pairingMap F τ (Q.X q)))
  (hQterms : InternalHomCechTotal.TermsAcyclic π U N Q.op)
  (a : P ⟶ Q)

def map (i j d : ℕ) (hi : d = i + c) (hj : d = j + c') :=
  (concentration π U hU N Q c' hPureQ j d hj).inv ≫
    HomologicalComplex.homologyMap
      (InternalHomTotalNaturality.totalMap π U N (Trace.SerreTotalNaturality.oppositeMap a)) d ≫
    (concentration π U hU N P c hPure i d hi).hom

theorem naturality (i j d : ℕ) (hi : d = i + c) (hj : d = j + c')
    {D₁ D₂ : ModuleCat.{u} R}
    (e₁ : (Trace.DualityHomology.coefficientComplex R F P).homology d ≅ D₁)
    (e₂ : (Trace.DualityHomology.coefficientComplex R F Q).homology d ≅ D₂)
    (b : D₁ ⟶ D₂)
    (he : HomologicalComplex.homologyMap (Trace.DualityHomologyNaturality.coefficientMap R F a) d ≫ e₂.hom =
      e₁.hom ≫ b) :
    map π U hU N c hPure c' hPureQ a i j d hi hj ≫
      (pairing π U hU N P c hPure R F τ hcover hP hPterms i d hi e₁).hom =
    (pairing π U hU N Q c' hPureQ R F τ hcover hQ hQterms j d hj e₂).hom ≫
      DualTransportNaturality.dualMap R b := by
  have h := Trace.SerreTotalNaturality.naturality π U R F N τ a hcover hP hQ hPterms hQterms d e₁ e₂ b he
  simp only [map, pairing, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg ((concentration π U hU N Q c' hPureQ j d hj).inv ≫ ·) h

theorem trace_naturality (i j d : ℕ) (hi : d = i + c) (hj : d = j + c')
    {D₁ D₂ : ModuleCat.{u} R}
    (e₁ : (Trace.DualityHomology.coefficientComplex R F P).homology d ≅ D₁)
    (e₂ : (Trace.DualityHomology.coefficientComplex R F Q).homology d ≅ D₂)
    (b : D₁ ⟶ D₂)
    (he : HomologicalComplex.homologyMap (Trace.DualityHomologyNaturality.coefficientMap R F a) d ≫ e₂.hom =
      e₁.hom ≫ b) (v₁ : D₁) (v₂ : D₂) (hv : b v₁ = v₂) :
    map π U hU N c hPure c' hPureQ a i j d hi hj ≫
      SerreUnitTrace.trace R (pairing π U hU N P c hPure R F τ hcover hP hPterms i d hi e₁) v₁ =
    SerreUnitTrace.trace R (pairing π U hU N Q c' hPureQ R F τ hcover hQ hQterms j d hj e₂) v₂ :=
  SerreUnitTrace.naturality R _ _ _ b v₁ v₂
    (naturality π U hU N c hPure R F τ hcover hP hPterms c' hPureQ hQ hQterms a
      i j d hi hj e₁ e₂ b he) hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureSerreMap
