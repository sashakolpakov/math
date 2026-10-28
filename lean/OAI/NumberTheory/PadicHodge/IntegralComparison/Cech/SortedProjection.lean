import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor

/-! # Sorted Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SortedProjection

noncomputable section

/-! Signed sorting acts as an actual cochain endomorphism on native
Čech cochains of any presheaf on a preorder. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category.{w} D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (P : Cᵒᵖ ⥤ D)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor

def component (n : ℕ) : (TupleRestrictionFunctor.complex U P).X n ⟶ (TupleRestrictionFunctor.complex U P).X n :=
  TupleRestrictionFunctor.map U P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjection n) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n)

theorem comm (n : ℕ) : component U P n ≫ (TupleRestrictionFunctor.complex U P).d n (n + 1) =
    (TupleRestrictionFunctor.complex U P).d n (n + 1) ≫ component U P (n + 1) := by
  rw [← TupleRestrictionFunctor.map_boundary U P n]
  unfold component
  rw [← TupleRestrictionFunctor.map_comp, ← TupleRestrictionFunctor.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact (AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternatingChainMap.cechTupleAlternatingProjection_boundary n x).symm

def endomorphism : TupleRestrictionFunctor.complex U P ⟶ TupleRestrictionFunctor.complex U P :=
  CochainComplex.ofHom (component U P) (comm U P)

theorem projection_injective (n : ℕ) (a : Fin (n + 1) → ι) (ha : Function.Injective a) :
    component U P n ≫ TupleRestrictionFunctor.projection U P a =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) •
        TupleRestrictionFunctor.rowBasis U P a (a ∘ Tuple.sort a) := by
  rw [component, TupleRestrictionFunctor.map_projection, AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjection_single,
    one_smul, AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjectionBasis_of_injective a ha, TupleRestrictionFunctor.row_single]

theorem projection_not_injective (n : ℕ) (a : Fin (n + 1) → ι) (ha : ¬ Function.Injective a) :
    component U P n ≫ TupleRestrictionFunctor.projection U P a = 0 := by
  rw [component, TupleRestrictionFunctor.map_projection, AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjection_single,
    one_smul, AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjectionBasis_of_not_injective a ha, map_zero]

theorem projection_strictMono (n : ℕ) (a : Fin (n + 1) → ι) (ha : StrictMono a) :
    component U P n ≫ TupleRestrictionFunctor.projection U P a = TupleRestrictionFunctor.projection U P a := by
  rw [component, TupleRestrictionFunctor.map_projection, AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjection_single, one_smul,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation.cechTupleAlternatingProjectionBasis_of_strictMono a ha, TupleRestrictionFunctor.row_single, one_smul,
    TupleRestrictionFunctor.rowBasis_of_subset U P a a Set.Subset.rfl, TupleRestrictionFunctor.restriction_self, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SortedProjection
