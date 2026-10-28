import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength
import Mathlib.RingTheory.QuotSMulTop

/-! # Parameter Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ParameterQuotient

noncomputable section

/-! Base change commutes with the actual scalar quotient module.
The native tensor-quotient equivalence needs no regularity or flatness
assumption. -/

open _root_.CategoryTheory

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} R) (r : R)

def iso :
    (Extension.baseChange R S).obj (.of R (QuotSMulTop r M)) ≅
      .of S (QuotSMulTop (algebraMap R S r) ((Extension.baseChange R S).obj M)) :=
  (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop r M S).symm.toModuleIso

theorem length (N : ModuleCat.{u} S)
    (e : (Extension.baseChange R S).obj M ≃ₗ[S] N) :
    FiltrationBaseLength.length R S (.of R (QuotSMulTop r M)) =
      Module.length S (QuotSMulTop (algebraMap R S r) N) :=
  (iso R S M r).toLinearEquiv.length_eq.trans
    (QuotSMulTop.congr (algebraMap R S r) e).length_eq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ParameterQuotient
