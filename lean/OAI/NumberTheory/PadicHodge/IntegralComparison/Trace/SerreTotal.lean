import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomology

/-! # Serre Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotal

noncomputable section

/-! Combine the abstract trace duality with the actual internal-Hom
Čech comparison before specializing any geometric terms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : X.Modules ⥤ ModuleCat.{u} R) [F.Additive]
  (N : X.Modules) (τ : F.obj N ⟶ ModuleCat.of R R)
  (P : ChainComplex X.Modules ℕ)

def iso (hU : iSup U = ⊤)
    (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
    (hterms : InternalHomCechTotal.TermsAcyclic π U N P.op)
    (n : ℕ) {D : ModuleCat.{u} R}
    (e : (DualityHomology.coefficientComplex R F P).homology n ≅ D) :
    InternalHomCechTotal.TotalIso π U N P.op n (DualHomologyTransport.dualGroup R D) :=
  InternalHomTotalTransport.transport π U N P.op hU hterms n
    (DualityHomology.homologyIsoTo R F τ P hP n e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotal
