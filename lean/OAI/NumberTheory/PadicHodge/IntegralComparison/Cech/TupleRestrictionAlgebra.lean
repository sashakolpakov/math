import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor

/-! # Tuple Restriction Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionAlgebra.Functor

noncomputable section

/-! Additive identities for the actual restriction maps attached to finite
integral tuple matrices. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category.{w} D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} (U : ι → C) (P : Cᵒᵖ ⥤ D)

theorem map_add_eq {n m : ℕ}
    (f g : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)
    (hf : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) (hg : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g) :
    TupleRestrictionFunctor.map U P (f + g) (hf.add hg) = TupleRestrictionFunctor.map U P f hf + TupleRestrictionFunctor.map U P g hg := by
  apply Pi.hom_ext
  intro (i : Fin (n + 1) → ι)
  change _ ≫ TupleRestrictionFunctor.projection U P i = _ ≫ TupleRestrictionFunctor.projection U P i
  rw [add_comp, TupleRestrictionFunctor.map_projection, TupleRestrictionFunctor.map_projection, TupleRestrictionFunctor.map_projection]
  exact (TupleRestrictionFunctor.row U P i).map_add _ _

theorem map_neg_eq {n m : ℕ}
    (f : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)
    (hf : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) :
    TupleRestrictionFunctor.map U P (-f) hf.neg = -TupleRestrictionFunctor.map U P f hf := by
  apply Pi.hom_ext
  intro (i : Fin (n + 1) → ι)
  change _ ≫ TupleRestrictionFunctor.projection U P i = _ ≫ TupleRestrictionFunctor.projection U P i
  rw [neg_comp, TupleRestrictionFunctor.map_projection, TupleRestrictionFunctor.map_projection]
  exact (TupleRestrictionFunctor.row U P i).map_neg _

theorem map_zero_eq (n m : ℕ)
    (h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing (0 : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)) :
    TupleRestrictionFunctor.map U P 0 h = 0 := by
  apply Pi.hom_ext
  intro (i : Fin (n + 1) → ι)
  change _ ≫ TupleRestrictionFunctor.projection U P i = _ ≫ TupleRestrictionFunctor.projection U P i
  rw [TupleRestrictionFunctor.map_projection, zero_comp]
  exact (TupleRestrictionFunctor.row U P i).map_zero

theorem map_id_eq (n : ℕ) :
    TupleRestrictionFunctor.map U P (LinearMap.id : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n)
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality.cechTupleSupportNonincreasing_id = 𝟙 _ := by
  apply Pi.hom_ext
  intro (i : Fin (n + 1) → ι)
  change _ ≫ TupleRestrictionFunctor.projection U P i = _ ≫ TupleRestrictionFunctor.projection U P i
  rw [TupleRestrictionFunctor.map_projection, Category.id_comp]
  change TupleRestrictionFunctor.row U P i (Finsupp.single i 1) = _
  rw [TupleRestrictionFunctor.row_single, one_smul, TupleRestrictionFunctor.rowBasis_of_subset U P i i Set.Subset.rfl,
    TupleRestrictionFunctor.restriction_self, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionAlgebra.Functor
