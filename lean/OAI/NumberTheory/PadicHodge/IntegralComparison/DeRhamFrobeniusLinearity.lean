import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FieldFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo

/-! # De Rham Frobenius Linearity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamFrobeniusLinearity

noncomputable section

/-!
# IntegralComparison: the ordinary de Rham differential is linear for the actual finite-field Frobenius action
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (k C : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C]

def generatorDerivation {n : ℕ} (v : Fin n → C) : Derivation k C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C (n + 1)) where
  __ := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.generatorDifferential k C v
  map_one_eq_zero' := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_cons_one k C v
  leibniz' a b := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_cons_mul k C a b v

theorem generator_frobenius {n : ℕ} (v : Fin n → C) (a : C) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k C 1 (Fin.cons ((FiniteField.frobeniusAlgHom k C) a) v) = 0 := by
  change generatorDerivation k C v (a ^ Fintype.card k) = 0
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, FiniteField.cast_card_eq_zero, zero_smul]

omit [Fintype k] in
theorem symbol_smul {n : ℕ} (a b : C) (v : Fin n → C) :
    a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k C b v = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k C (a * b) v := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one k C b v, smul_smul, ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

theorem differential_frobenius_smul (n : ℕ) (a : C) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential k C n ((FiniteField.frobeniusAlgHom k C a) • ω) =
      (FiniteField.frobeniusAlgHom k C a) • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential k C n ω := by
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations k C n) ω
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s t hs ht => simp only [map_add, smul_add, hs, ht]
  | single v b =>
      change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential k C n ((FiniteField.frobeniusAlgHom k C a) • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k C b v) =
        (FiniteField.frobeniusAlgHom k C a) • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential k C n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k C b v)
      rw [symbol_smul, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_cons_mul, generator_frobenius, smul_zero,
        add_zero, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamFrobeniusLinearity
