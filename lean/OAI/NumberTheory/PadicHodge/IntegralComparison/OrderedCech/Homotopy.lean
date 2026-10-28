import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Retraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopyIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport
import Mathlib.Algebra.Homology.Homotopy

/-! # Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Homotopy

noncomputable section

/-! Signed sorting is a homotopy equivalence for the actual Čech complex
of any additive presheaf on a preorder. No finiteness of the cover is needed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (P : Cᵒᵖ ⥤ D)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionAlgebra.Functor

def component (n : ℕ) : (Cech.TupleRestrictionFunctor.complex U P).X (n + 1) ⟶ (Cech.TupleRestrictionFunctor.complex U P).X n :=
  Cech.TupleRestrictionFunctor.map U P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportNonincreasing n)

private def previous (n : ℕ) : (Cech.TupleRestrictionFunctor.complex U P).X n ⟶ (Cech.TupleRestrictionFunctor.complex U P).X n :=
  Cech.TupleRestrictionFunctor.map U P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious n)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality.cechTupleAlternatingHomotopyPrevious_supportNonincreasing n)

private theorem identity (n : ℕ) :
    (Cech.TupleRestrictionFunctor.complex U P).d n (n + 1) ≫ component U P n + previous U P n =
      Cech.SortedProjection.component U P n - 𝟙 _ := by
  rw [← Cech.TupleRestrictionFunctor.map_boundary U P n]
  unfold component previous Cech.SortedProjection.component
  rw [← Cech.TupleRestrictionFunctor.map_comp]
  apply Pi.hom_ext
  intro (i : Fin (n + 1) → ι)
  change _ ≫ Cech.TupleRestrictionFunctor.projection U P i = _ ≫ Cech.TupleRestrictionFunctor.projection U P i
  rw [add_comp, sub_comp, Category.id_comp,
    Cech.TupleRestrictionFunctor.map_projection, Cech.TupleRestrictionFunctor.map_projection, Cech.TupleRestrictionFunctor.map_projection]
  have hi : Cech.TupleRestrictionFunctor.projection U P i = Cech.TupleRestrictionFunctor.row U P i (Finsupp.single i 1) := by
    rw [Cech.TupleRestrictionFunctor.row_single, one_smul, Cech.TupleRestrictionFunctor.rowBasis_of_subset U P i i Set.Subset.rfl,
      Cech.TupleRestrictionFunctor.restriction_self, Category.comp_id]
  rw [hi, ← map_add, ← map_sub]
  exact congrArg (Cech.TupleRestrictionFunctor.row U P i)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopyIdentity.cechTupleAlternatingHomotopy_identity n (Finsupp.single i 1))

private theorem previous_zero : previous U P 0 = 0 := by
  unfold previous
  exact Cech.TupleRestrictionAlgebra.Functor.map_zero_eq U P 0 0 _

private theorem previous_succ (n : ℕ) :
    previous U P (n + 1) = component U P n ≫ (Cech.TupleRestrictionFunctor.complex U P).d n (n + 1) := by
  rw [← Cech.TupleRestrictionFunctor.map_boundary U P n]
  unfold previous component
  rw [← Cech.TupleRestrictionFunctor.map_comp]
  congr 1

private def homotopyComponent (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (Cech.TupleRestrictionFunctor.complex U P).X i ⟶ (Cech.TupleRestrictionFunctor.complex U P).X j := by
  change j + 1 = i at h
  subst i
  exact component U P j

private def nullMap : Cech.TupleRestrictionFunctor.complex U P ⟶ Cech.TupleRestrictionFunctor.complex U P :=
  Homotopy.nullHomotopicMap' (homotopyComponent U P)

private theorem nullMap_zero : (nullMap U P).f 0 =
    (Cech.TupleRestrictionFunctor.complex U P).d 0 1 ≫ component U P 0 := by
  rw [nullMap, Homotopy.nullHomotopicMap'_f_of_not_rel_right
    (ComplexShape.up_mk 0 1 rfl)]
  · rfl
  · intro l hl
    change l + 1 = 0 at hl
    omega

private theorem nullMap_succ (n : ℕ) : (nullMap U P).f (n + 1) =
    (Cech.TupleRestrictionFunctor.complex U P).d (n + 1) (n + 2) ≫ component U P (n + 1) +
      component U P n ≫ (Cech.TupleRestrictionFunctor.complex U P).d n (n + 1) := by
  rw [nullMap, Homotopy.nullHomotopicMap'_f
    (ComplexShape.up_mk n (n + 1) rfl) (ComplexShape.up_mk (n + 1) (n + 2) rfl)]
  rfl

private theorem nullMap_eq : nullMap U P =
    Projection.map U P ≫ Retraction.inclusion U P - 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  change (nullMap U P).f n =
    Projection.mapF U P n ≫ Retraction.inclusionF U P n - 𝟙 _
  rw [Retraction.mapF_inclusionF]
  cases n with
  | zero =>
    rw [nullMap_zero]
    simpa only [previous_zero, add_zero] using identity U P 0
  | succ n =>
    rw [nullMap_succ]
    simpa only [previous_succ] using identity U P (n + 1)

def homotopy : Homotopy
    (Projection.map U P ≫ Retraction.inclusion U P)
    (𝟙 (Cech.TupleRestrictionFunctor.complex U P)) := by
  refine Homotopy.equivSubZero.symm ?_
  refine (Homotopy.ofEq (nullMap_eq U P).symm).trans ?_
  exact Homotopy.nullHomotopy' (homotopyComponent U P)

def equiv : HomotopyEquiv (Cech.TupleRestrictionFunctor.complex U P) (Projection.complex U P) where
  hom := Projection.map U P
  inv := Retraction.inclusion U P
  homotopyHomInvId := homotopy U P
  homotopyInvHomId := Homotopy.ofEq (Retraction.inclusion_map U P)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Homotopy
