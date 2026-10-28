import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD

/-! # De Rham Symbol -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSymbol.DeRhamSymbolPowers

noncomputable section

/-! # Power substitution in the actual integral differential symbols -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem symbol_powers (n : ℕ) (a : A) (v : Fin n → A) (m : Fin n → ℕ) :
    DeRhamPresentationTo.DeRhamPresentation.symbol R A a (fun i => v i ^ m i) =
      DeRhamPresentationTo.DeRhamPresentation.symbol R A
        (a * ∏ i, (m i : A) * v i ^ (m i - 1)) v := by
  calc
    _ = a • FormsEquivalenceD.FormsEquivalence.liftedSymbols R A n
        (fun i => KaehlerDifferential.D R A (v i ^ m i)) := by
      rw [FormsEquivalenceD.FormsEquivalence.liftedSymbols_D, DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]
    _ = a • ((∏ i, (m i : A) * v i ^ (m i - 1)) •
        FormsEquivalenceD.FormsEquivalence.liftedSymbols R A n (fun i => KaehlerDifferential.D R A (v i))) := by
      congr 1
      simpa only [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, smul_smul] using
        (FormsEquivalenceD.FormsEquivalence.liftedSymbols R A n).map_smul_univ
          (fun i => (m i : A) * v i ^ (m i - 1))
          (fun i => KaehlerDifferential.D R A (v i))
    _ = _ := by
      rw [FormsEquivalenceD.FormsEquivalence.liftedSymbols_D, smul_smul, ← DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSymbol.DeRhamSymbolPowers
