import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SingularSet

/-! # Cech Cover Rows -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CechCoverRows

noncomputable section

/-!
# A Čech row resolution of small singular simplices

The projection from the disjoint union of a set cover has a section. Its
augmented Čech nerve therefore has an extra degeneracy, and applying the free
module functor gives a chain homotopy equivalence to the covered set in degree
zero. We apply this to the actual singular simplices whose images lie in at
least one member of a family of subsets.

This is a row resolution only. It does not identify the full singular complex
with its small-simplex subcomplex and does not assert a nerve theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

universe u

variable {α ι : Type u}

/-- The actual projection from the disjoint union of a family of subsets. -/
def coverProjection (U : ι → Set α) : (Σ i, U i) ⟶ α :=
  TypeCat.ofHom (fun z => z.2.1)

/-- The projection is surjective precisely when the subsets cover. -/
theorem coverProjection_surjective (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) : Function.Surjective (coverProjection U) := by
  intro x
  obtain ⟨i, hi⟩ := hU x
  exact ⟨⟨i, x, hi⟩, rfl⟩

/-- A set-theoretic section of a covering projection. -/
def coverProjectionSplit (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    SplitEpi (coverProjection U) where
  section_ := TypeCat.ofHom (fun x =>
    ⟨Classical.choose (hU x), x, Classical.choose_spec (hU x)⟩)
  id := by
    ext x
    rfl

/-- The augmented Čech nerve of the actual covering projection. -/
def coverCechNerve (U : ι → Set α) : SimplicialObject.Augmented (Type u) :=
  (Arrow.mk (coverProjection U)).augmentedCechNerve

/-- The chosen section supplies an extra degeneracy, with all identities proved
by mathlib's split Čech nerve construction. -/
def coverCechExtraDegeneracy (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    SimplicialObject.Augmented.ExtraDegeneracy (coverCechNerve U) :=
  Arrow.AugmentedCechNerve.extraDegeneracy
    (Arrow.mk (coverProjection U)) (coverProjectionSplit U hU)

variable (R : Type u) [Ring R]

/-- Free-module Čech chains of the projection from the disjoint union. -/
def coverCechModuleNerve (U : ι → Set α) :
    SimplicialObject.Augmented (ModuleCat R) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free R)).obj
    (coverCechNerve U)

/-- The alternating face complex resolving the covered set. -/
def coverCechChains (U : ι → Set α) : ChainComplex (ModuleCat R) ℕ :=
  AlternatingFaceMapComplex.obj (coverCechModuleNerve R U).left

/-- The augmented Čech chain resolution of a set cover contracts onto the free
module on the covered set, concentrated in degree zero. -/
def coverCechHomotopyEquiv (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    HomotopyEquiv (coverCechChains R U)
      ((ChainComplex.single₀ (ModuleCat R)).obj ((ModuleCat.free R).obj α)) :=
  ((coverCechExtraDegeneracy U hU).map (ModuleCat.free R)).homotopyEquiv

/-- Positive homology vanishes in this actual Čech row complex. -/
theorem coverCech_exactAt_succ (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) (k : ℕ) :
    (coverCechChains R U).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso
    (ChainComplex.exactAt_succ_single_obj ((ModuleCat.free R).obj α) k).isZero_homology
    ((coverCechHomotopyEquiv R U hU).toHomologyIso (k + 1))

/-- The zeroth homology of the Čech row is the free module on the covered set. -/
def coverCechHomologyZeroIso (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    (coverCechChains R U).homology 0 ≅ (ModuleCat.free R).obj α :=
  (coverCechHomotopyEquiv R U hU).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 ((ModuleCat.free R).obj α)

variable (X : TopCat.{u}) (U : ι → Set X) (n : ℕ)

/-- Actual singular n-simplices whose image is contained in one cover member. -/
def SmallSingularSimplex :=
  {σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌) //
    ∃ i, Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ) ⊆ U i}

/-- The member of the simplex cover corresponding to the spatial subset U i. -/
def smallSingularSimplexCover (i : ι) : Set (SmallSingularSimplex X U n) :=
  {σ | Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ.1) ⊆ U i}

/-- Smallness supplies the required covering property, without an extra
topological or comparison assumption. -/
theorem smallSingularSimplexCover_covers (σ : SmallSingularSimplex X U n) :
    ∃ i, σ ∈ smallSingularSimplexCover X U n i :=
  σ.2

/-- The actual Čech row of free modules on small singular n-simplices is chain
homotopy equivalent to the free module on those simplices in degree zero. -/
def smallSingularCechHomotopyEquiv :
    HomotopyEquiv (coverCechChains R (smallSingularSimplexCover X U n))
      ((ChainComplex.single₀ (ModuleCat R)).obj
        ((ModuleCat.free R).obj (SmallSingularSimplex X U n))) :=
  coverCechHomotopyEquiv R (smallSingularSimplexCover X U n)
    (smallSingularSimplexCover_covers X U n)

/-- Every positive Čech degree in a fixed singular-simplex row is exact. -/
theorem smallSingularCech_exactAt_succ (k : ℕ) :
    (coverCechChains R (smallSingularSimplexCover X U n)).ExactAt (k + 1) :=
  coverCech_exactAt_succ R (smallSingularSimplexCover X U n)
    (smallSingularSimplexCover_covers X U n) k

end

end OAI.AlgebraicTopology.DeRham.Comparison.CechCoverRows
