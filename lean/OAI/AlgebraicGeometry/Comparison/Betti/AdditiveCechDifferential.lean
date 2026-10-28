import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr

/-! # Additive Cech Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechDifferential

noncomputable section

/-! Additive evaluation of the original Čech differential is the alternating
sum of the original cosimplicial cofaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

variable {X ι : Type} [TopologicalSpace X]
  (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) (U : ι → Opens X)

theorem additiveCechDifferential_eq (q : ℕ) :
    ((cechComplexFunctor U).obj F).d q (q + 1) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).map
          (SimplexCategory.δ k)) := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.obj
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)).d q (q + 1) = _
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  rfl

theorem additiveCechDifferential_eval {A : Type} [AddCommGroup A] (q : ℕ)
    (H : ((cechComplexFunctor U).obj F).X (q + 1) →+ A)
    (z : ((cechComplexFunctor U).obj F).X q) :
    H (((cechComplexFunctor U).obj F).d q (q + 1) z) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        H ((((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).map
          (SimplexCategory.δ k)) z) := by
  let ev : (((cechComplexFunctor U).obj F).X q ⟶ ((cechComplexFunctor U).obj F).X (q + 1)) →+
      ((cechComplexFunctor U).obj F).X (q + 1) :=
    { toFun := fun f => f z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact (congrArg (fun f => (H.comp ev) f) (additiveCechDifferential_eq F U q)).trans
    ((map_sum (H.comp ev) _ Finset.univ).trans
      (Finset.sum_congr rfl (fun k _ => map_zsmul (H.comp ev) ((-1 : ℤ) ^ k.val) _)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechDifferential
