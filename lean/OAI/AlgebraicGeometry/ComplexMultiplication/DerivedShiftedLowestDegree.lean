import OAI.AlgebraicGeometry.ComplexMultiplication.DerivedLowestDegree
import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalSections

/-! # Derived Shifted Lowest Degree -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.DerivedShiftedLowestDegree

noncomputable section

/-! # Lowest-degree classes have actual shifted complex representatives -/

open _root_.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Shifting the actual target gives representatives in the original degree. -/
theorem shiftedDerivedMap_surjective_from_single (A : C) (K : CochainComplex C ℤ)
    (n : ℤ) [K.IsStrictlyGE n] :
    Function.Surjective
      (fun f : ShiftedHom ((CochainComplex.singleFunctor C 0).obj A) K n =>
        f.map DerivedCategory.Q) := by
  intro f
  let e := (DerivedCategory.Q.commShiftIso n).app K
  let : (K⟦n⟧).IsStrictlyGE 0 := K.isStrictlyGE_shift n n 0 (by simp)
  obtain ⟨g, hg⟩ := DerivedLowestDegree.derivedMap_surjective_from_single A (K⟦n⟧) 0 (f ≫ e.inv)
  change DerivedCategory.Q.map g = f ≫ e.inv at hg
  refine ⟨g, ?_⟩
  change DerivedCategory.Q.map g ≫ e.hom = f
  rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.DerivedShiftedLowestDegree
