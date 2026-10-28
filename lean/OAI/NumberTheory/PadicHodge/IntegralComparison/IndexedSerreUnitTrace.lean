import OAI.NumberTheory.PadicHodge.IntegralComparison.SerreUnitTrace

/-! # Indexed Serre Unit Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedSerreUnitTrace

noncomputable section

/-! Transport a Serre pairing to degree zero before evaluating at the
actual unit. This keeps the degree equality separate from the geometry. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (V : ℕ → ModuleCat.{u} R)
  {A : AddCommGrpCat.{u}} {n : ℕ}

def pairing (p : A ≅ DualHomologyTransport.dualGroup R (V n)) (h : n = 0) :
    A ≅ DualHomologyTransport.dualGroup R (V 0) :=
  DualHomologyTransport.transport R p (eqToIso (congrArg V h))

def traceIso (p : A ≅ DualHomologyTransport.dualGroup R (V n)) (h : n = 0)
    (e : R ≃ₗ[R] V 0) : A ≅ AddCommGrpCat.of R :=
  SerreUnitTrace.traceIso R (pairing R V p h) e

@[simp]
theorem traceIso_hom (p : A ≅ DualHomologyTransport.dualGroup R (V n)) (h : n = 0)
    (e : R ≃ₗ[R] V 0) :
    (traceIso R V p h e).hom = SerreUnitTrace.trace R (pairing R V p h) (e 1) :=
  SerreUnitTrace.traceIso_hom R (pairing R V p h) e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedSerreUnitTrace
