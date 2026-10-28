import OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra

/-! # Tuple Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.TupleCech.TupleCechExact

noncomputable section

/-!
# Positive exactness of tuple nerves with arbitrary coefficients

The coproduct of copies of an abelian-category object over each tuple
nerve is exact in positive degrees. A point gives a contraction when the
index set is nonempty; an empty index set gives zero in every degree.
No covering or nonemptiness assumption is required for positive exactness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

universe u v w

variable (A : Type u) [Category.{v} A] [Abelian A] [HasCoproducts.{w} A] (M : A)

def augmented (S : Type w) : SimplicialObject.Augmented A :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (sigmaConst.obj M)).obj
    (NonemptyCechExtra.NonemptyCechNerve.augmented S)

def complex (S : Type w) : ChainComplex A ℕ :=
  (alternatingFaceMapComplex A).obj (augmented A M S).left

def homotopyEquiv (S : Type w) (s : S) :
    HomotopyEquiv (complex A M S) ((ChainComplex.single₀ A).obj (augmented A M S).right) :=
  ((NonemptyCechExtra.NonemptyCechNerve.extraDegeneracy S s).map (sigmaConst.obj M)).homotopyEquiv

theorem exactAt (S : Type w) (n : ℕ) (hn : n ≠ 0) : (complex A M S).ExactAt n := by
  by_cases hS : Nonempty S
  · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (augmented A M S).right n hn
    have ht := HomologicalComplex.ExactAt.of_isZero hz
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ht.isZero_homology.of_iso ((TupleCechExact.homotopyEquiv A M S (Classical.choice hS)).toHomologyIso n)
  · apply HomologicalComplex.ExactAt.of_isZero
    rw [IsZero.iff_id_eq_zero]
    change (𝟙 (∐ (fun (_ : Fin (n + 1) → S) => M))) = 0
    apply Sigma.hom_ext
    intro f
    exact (hS ⟨f 0⟩).elim

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.TupleCech.TupleCechExact
