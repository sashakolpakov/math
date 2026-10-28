import OAI.AlgebraicGeometry.Comparison.Betti.Target
import OAI.Analysis.HodgeTheory.Decomposition.Core

/-! # Hodge Bidegree Index -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HodgeBidegreeIndex

noncomputable section

/-!
The two independently defined Hodge filtrations use different indices and
different presentations of degree transport. This module identifies their
actual pure Betti subspaces without assuming any comparison theorem.
-/

open _root_.CategoryTheory

/-- A bidegree of total degree `n` is determined by its first coordinate. -/
def hodgeBidegreeFinEquiv (n : ℕ) : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n ≃ Fin (n + 1) where
  toFun i := ⟨i.val.1, by have := i.property; omega⟩
  invFun p := ⟨(p, n - p), Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt)⟩
  left_inv i := by
    apply Subtype.ext
    have := i.property
    apply Prod.ext
    · rfl
    · dsimp
      omega
  right_inv p := by rfl

/-- Mapping a pure subspace along degree equality is the original HodgeDecomposition cast. -/
theorem pureBetti_map_degree_eq_hodgePiece (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p q n : ℕ) (h : p + q = n) :
    (P.pureBettiSubspace p q).map
      ((eqToHom (congrArg P.complexCohomology h)) :
        P.complexCohomology (p + q) ⟶ P.complexCohomology n).hom =
      Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P n ⟨(p, q), h⟩ := by
  subst n
  change (P.pureBettiSubspace p q).map LinearMap.id = P.pureBettiSubspace p q
  exact Submodule.map_id _

theorem projectivePureBettiInDegree_eq_hodgePiece
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (p : Fin (n + 1)) :
    Target.projectivePureBettiInDegree P n p =
      Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P n ((hodgeBidegreeFinEquiv n).symm p) :=
  pureBetti_map_degree_eq_hodgePiece P p (n - p) n _

/-- The sums of the same actual pure subspaces agree under the finite index. -/
theorem projectivePureBetti_iSup_eq_hodgePiece_iSup
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (r : ℤ) :
    (⨆ (p : Fin (n + 1)) (_ : r ≤ (p : ℤ)), Target.projectivePureBettiInDegree P n p) =
      ⨆ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (_ : r ≤ (i.val.1 : ℤ)),
        Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P n i := by
  simp only [projectivePureBettiInDegree_eq_hodgePiece]
  have hfirst (p : Fin (n + 1)) :
      ((hodgeBidegreeFinEquiv n).symm p).val.1 = p.val := rfl
  have hsum := (hodgeBidegreeFinEquiv n).symm.iSup_comp
    (g := fun i => ⨆ (_ : r ≤ (i.val.1 : ℤ)), Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P n i)
  simpa only [hfirst] using hsum

end

end OAI.AlgebraicGeometry.Comparison.Betti.HodgeBidegreeIndex
