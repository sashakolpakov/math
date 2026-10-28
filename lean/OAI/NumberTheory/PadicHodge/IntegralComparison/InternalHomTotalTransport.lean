import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal

/-! # Internal Hom Total Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalTransport

noncomputable section

/-! Transport through the Čech comparison with named source and target
isomorphism types, so specializations retain the generic constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (N : X.Modules) (K : CochainComplex X.Modulesᵒᵖ ℕ)

def HomologyTo (n : ℕ) (D : AddCommGrpCat.{u}) := (InternalHomCechTotal.homComplex N K).homology n ≅ D

def transport (hU : iSup U = ⊤) (hK : InternalHomCechTotal.TermsAcyclic π U N K)
    (n : ℕ) {D : AddCommGrpCat.{u}} (e : HomologyTo N K n D) :
    InternalHomCechTotal.TotalIso π U N K n D :=
  (InternalHomCechTotal.comparison π U N K hU hK n).symm ≪≫ e

def ChainHomologyTo (P : ChainComplex X.Modules ℕ) (n : ℕ) (D : AddCommGrpCat.{u}) :=
  (((preadditiveYoneda.obj N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj P.op).homology n ≅ D

def ofChain (P : ChainComplex X.Modules ℕ) (n : ℕ) {D : AddCommGrpCat.{u}}
    (e : ChainHomologyTo N P n D) : HomologyTo N P.op n D := e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalTransport
