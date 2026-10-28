import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.FiniteTerms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Nat.Choose.Basic

/-! # Term Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.TermRanks

noncomputable section

/-! The terms of the explicit scalar Koszul complex have the binomial ranks. The induction follows its actual mapping-cone direct-sum decomposition. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] [Nontrivial R]

theorem scalarKoszulComplex_term_finrank (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Free R M] (rs : List R) :
    ∀ q : ℕ, Module.finrank R ((KoszulComplex.scalarKoszulComplex M rs).X (-(q : ℤ))) =
      rs.length.choose q * Module.finrank R M := by
  induction rs with
  | nil =>
    intro q
    cases q with
    | zero =>
      change Module.finrank R ((KoszulComplex.scalarKoszulComplex M []).X 0) = _
      simpa only [List.length_nil, Nat.choose_zero_right, one_mul] using
        (FiniteTerms.scalarKoszulZeroTermIso M []).toLinearEquiv.finrank_eq
    | succ q =>
      have : Subsingleton ((KoszulComplex.scalarKoszulComplex M []).X (-((q + 1 : ℕ) : ℤ))) :=
        ModuleCat.subsingleton_of_isZero
          (KoszulComplex.scalarKoszulComplex_isZero_X M [] _ (Or.inl (by simp; omega)))
      rw [Module.finrank_zero_of_subsingleton, List.length_nil, Nat.choose_zero_succ, zero_mul]
  | cons r rs ih =>
    intro q
    cases q with
    | zero =>
      change Module.finrank R ((KoszulComplex.scalarKoszulComplex M (r :: rs)).X 0) = _
      simpa only [Nat.choose_zero_right, one_mul] using
        (FiniteTerms.scalarKoszulZeroTermIso M (r :: rs)).toLinearEquiv.finrank_eq
    | succ q =>
      let i : ℤ := -((q + 1 : ℕ) : ℤ)
      have hi : i + 1 = -(q : ℤ) := by dsimp [i]; omega
      have : Module.Finite R ((KoszulComplex.scalarKoszulComplex M rs).X (i + 1)) :=
        (FiniteTerms.scalarKoszulComplex_finite_free M rs (i + 1)).1
      have : Module.Free R ((KoszulComplex.scalarKoszulComplex M rs).X (i + 1)) :=
        (FiniteTerms.scalarKoszulComplex_finite_free M rs (i + 1)).2
      have : Module.Finite R ((KoszulComplex.scalarKoszulComplex M rs).X i) :=
        (FiniteTerms.scalarKoszulComplex_finite_free M rs i).1
      have : Module.Free R ((KoszulComplex.scalarKoszulComplex M rs).X i) :=
        (FiniteTerms.scalarKoszulComplex_finite_free M rs i).2
      calc
        Module.finrank R ((KoszulComplex.scalarKoszulComplex M (r :: rs)).X i) =
            Module.finrank R ((KoszulComplex.scalarKoszulComplex M rs).X (i + 1) ×
              (KoszulComplex.scalarKoszulComplex M rs).X i) := (FiniteTerms.scalarKoszulConsTermIso M r rs i).toLinearEquiv.finrank_eq
        _ = Module.finrank R ((KoszulComplex.scalarKoszulComplex M rs).X (-(q : ℤ))) +
              Module.finrank R ((KoszulComplex.scalarKoszulComplex M rs).X (-((q + 1 : ℕ) : ℤ))) := by
            rw [Module.finrank_prod, hi]
        _ = (r :: rs).length.choose (q + 1) * Module.finrank R M := by
            rw [ih q, ih (q + 1), List.length_cons, Nat.choose_succ_succ, add_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.TermRanks
