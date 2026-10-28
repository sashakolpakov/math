import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondFiniteness
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # Total Second Reference Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondReferenceFiniteness.Reference

noncomputable section

/-! Second-stage finiteness for the original orientation of a first-quadrant total complex. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

theorem finite (n : ℕ)
    (h : ∀ q p, q + p = n → Module.Finite R
      ((TotalSecondClasses.horizontal K.flip p).homology q)) :
    Module.Finite R ((K.total (.up ℕ)).homology n) := by
  let : Module.Finite R ((K.flip.total (.up ℕ)).homology n) :=
    TotalSecondFiniteness.finite K.flip n h
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (K.totalFlipIso (.up ℕ)) n).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondReferenceFiniteness.Reference
