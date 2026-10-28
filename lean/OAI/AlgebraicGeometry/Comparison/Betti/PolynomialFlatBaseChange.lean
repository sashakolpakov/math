import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.PolynomialAlgebra

/-! # Polynomial Flat Base Change -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PolynomialFlatBaseChange.AnalyticLocal

noncomputable section

/-! Coefficientwise polynomial extension preserves a flat ring map. -/

open _root_.Polynomial

universe u

theorem polynomial_map_flat {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) : (Polynomial.mapRingHom f).Flat := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R[X] S[X] := Polynomial.algebra R S
  exact RingHom.Flat.isStableUnderBaseChange R S R[X] S[X] hf

end

end OAI.AlgebraicGeometry.Comparison.Betti.PolynomialFlatBaseChange.AnalyticLocal
