import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor

/-! # Tuple Restriction Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionNaturality.Functor

noncomputable section

/-! Finite tuple-matrix restriction maps are natural in the coefficient
presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category.{w} D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} (U : ι → C) {P Q : Cᵒᵖ ⥤ D} (a : P ⟶ Q)

abbrev coefficientMap := (NonemptyCechNerve.complexFunctor U).map a

theorem coefficientMap_projection {n : ℕ} (i : Fin (n + 1) → ι) :
    (coefficientMap U a).f n ≫ TupleRestrictionFunctor.projection U Q i =
      TupleRestrictionFunctor.projection U P i ≫ a.app (op (∏ᶜ (U ∘ i))) := by
  exact Pi.map_π (fun j : Fin (n + 1) → ι => a.app (op (∏ᶜ (U ∘ j)))) i

theorem rowBasis_naturality {n m : ℕ} (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) :
    (coefficientMap U a).f m ≫ TupleRestrictionFunctor.rowBasis U Q i j =
      TupleRestrictionFunctor.rowBasis U P i j ≫ a.app (op (∏ᶜ (U ∘ i))) := by
  classical
  by_cases h : Set.range j ⊆ Set.range i
  · rw [TupleRestrictionFunctor.rowBasis_of_subset U Q i j h, TupleRestrictionFunctor.rowBasis_of_subset U P i j h,
      ← Category.assoc, coefficientMap_projection, Category.assoc]
    exact (congrArg (fun z => TupleRestrictionFunctor.projection U P j ≫ z) (a.naturality (TupleRestrictionFunctor.inclusion U i j h).op).symm).trans
      (Category.assoc _ _ _).symm
  · simp only [TupleRestrictionFunctor.rowBasis, dite_eq_right h, comp_zero, zero_comp]

theorem row_naturality {n m : ℕ} (i : Fin (n + 1) → ι) (x : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m) :
    (coefficientMap U a).f m ≫ TupleRestrictionFunctor.row U Q i x =
      TupleRestrictionFunctor.row U P i x ≫ a.app (op (∏ᶜ (U ∘ i))) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, comp_zero, zero_comp]
  | add x y hx hy => simp only [map_add, comp_add, add_comp, hx, hy]
  | single j z => rw [TupleRestrictionFunctor.row_single, TupleRestrictionFunctor.row_single, comp_zsmul, zsmul_comp, rowBasis_naturality]

theorem map_naturality {n m : ℕ}
    (f : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)
    (hf : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) :
    (coefficientMap U a).f m ≫ TupleRestrictionFunctor.map U Q f hf =
      TupleRestrictionFunctor.map U P f hf ≫ (coefficientMap U a).f n := by
  apply Pi.hom_ext
  intro (i : Fin (n + 1) → ι)
  change _ ≫ TupleRestrictionFunctor.projection U Q i = _ ≫ TupleRestrictionFunctor.projection U Q i
  rw [Category.assoc, TupleRestrictionFunctor.map_projection, Category.assoc, coefficientMap_projection,
    ← Category.assoc, TupleRestrictionFunctor.map_projection]
  exact row_naturality U a i _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionNaturality.Functor
