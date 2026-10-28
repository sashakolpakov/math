import OAI.AlgebraicTopology.DeRham.Comparison.CechCoverRows
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-! # Small Singular Set -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet

noncomputable section

/-!
# Singular simplices subordinate to a family of subsets

Precomposing a singular simplex by any simplicial operator does not enlarge its
image. Thus the simplices contained in some member of a given family form a
genuine subcomplex of mathlib's singular simplicial set.

No subdivision or quasi-isomorphism assertion is made here.
-/

open _root_.CategoryTheory
open scoped Simplicial

universe u

variable (X : TopCat.{u})

/-- A simplicial operator restricts the image of an actual singular simplex. -/
theorem singularSimplex_range_map_subset
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (σ : (TopCat.toSSet.obj X).obj n) :
    Set.range (X.toSSetObjEquiv m ((TopCat.toSSet.obj X).map f σ)) ⊆
      Set.range (X.toSSetObjEquiv n σ) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨((SimplexCategory.toTop.{u}.map f.unop) (ULift.up x)).down, ?_⟩
  rfl

variable {ι κ : Type u} (U : ι → Set X)

/-- The actual simplicial subcomplex of simplices contained in a cover member. -/
def smallSingularSubcomplex : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i}
  map f σ hσ := by
    obtain ⟨i, hi⟩ := hσ
    exact ⟨i, (singularSimplex_range_map_subset X f σ).trans hi⟩

/-- Membership is the standard image-containment condition. -/
@[simp]
theorem mem_smallSingularSubcomplex {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (smallSingularSubcomplex X U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i := Iff.rfl

/-- The inclusion is the actual canonical inclusion of a simplicial subcomplex. -/
def smallSingularInclusion :
    (smallSingularSubcomplex X U : SSet) ⟶ TopCat.toSSet.obj X :=
  (smallSingularSubcomplex X U).ι

instance smallSingularInclusion_mono : Mono (smallSingularInclusion X U) := by
  unfold smallSingularInclusion
  infer_instance

/-- Degreewise identification with the simplex type resolved by CechCoverRows. -/
def smallSingularDegreeEquiv (n : ℕ) :
    ((smallSingularSubcomplex X U : SSet).obj (.op ⦋n⦌)) ≃
      CechCoverRows.SmallSingularSimplex X U n :=
  Equiv.refl _

/-- Refining the family can only enlarge the small singular subcomplex. -/
theorem smallSingularSubcomplex_le_of_refinement (V : κ → Set X)
    (h : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularSubcomplex X U ≤ smallSingularSubcomplex X V := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨j, hj⟩ := h i
  exact ⟨j, hi.trans hj⟩

/-- Pointwise inclusion is a special case of refinement. -/
theorem smallSingularSubcomplex_mono (V : ι → Set X) (h : ∀ i, U i ⊆ V i) :
    smallSingularSubcomplex X U ≤ smallSingularSubcomplex X V :=
  smallSingularSubcomplex_le_of_refinement X U V (fun i => ⟨i, h i⟩)

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet
