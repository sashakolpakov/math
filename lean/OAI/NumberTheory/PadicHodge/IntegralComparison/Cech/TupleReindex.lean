import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange

/-! # Tuple Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleReindex

noncomputable section

/-! The finite signed tuple maps commute with finite-limit-preserving
reindexing, through the original product comparison isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι : Type u} (U : ι → C)
  {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]
  (P : Dᵒᵖ ⥤ A)

def factorIso {n : ℕ} (a : Fin (n+1) → ι) :
    TupleRestrictionFunctor.factor U (r.op ⋙ P) a ≅ TupleRestrictionFunctor.factor (r.obj ∘ U) P a :=
  P.mapIso (PreservesProduct.iso r (U ∘ a)).symm.op

abbrev componentIso (n : ℕ) := AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.componentIso r U P ⦋n⦌

theorem component_projection {n : ℕ} (a : Fin (n+1) → ι) :
    (componentIso r U P n).hom ≫ TupleRestrictionFunctor.projection (r.obj ∘ U) P a =
      TupleRestrictionFunctor.projection U (r.op ⋙ P) a ≫ (factorIso r U P a).hom :=
  Pi.mapIso_hom_π _ _

omit [Preadditive A] [HasProducts A] in
theorem restriction_naturality {n m : ℕ}
    (a : Fin (n+1) → ι) (b : Fin (m+1) → ι) (h : Set.range b ⊆ Set.range a) :
    TupleRestrictionFunctor.restriction U (r.op ⋙ P) a b h ≫ (factorIso r U P a).hom =
      (factorIso r U P b).hom ≫ TupleRestrictionFunctor.restriction (r.obj ∘ U) P a b h := by
  change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
  exact (P.map_comp _ _).symm.trans
    ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

theorem rowBasis_naturality {n m : ℕ} (a : Fin (n+1) → ι) (b : Fin (m+1) → ι) :
    (componentIso r U P m).hom ≫ TupleRestrictionFunctor.rowBasis (r.obj ∘ U) P a b =
      TupleRestrictionFunctor.rowBasis U (r.op ⋙ P) a b ≫ (factorIso r U P a).hom := by
  classical
  by_cases h : Set.range b ⊆ Set.range a
  · rw [TupleRestrictionFunctor.rowBasis_of_subset _ _ _ _ h, TupleRestrictionFunctor.rowBasis_of_subset _ _ _ _ h,
      ← Category.assoc, component_projection, Category.assoc,
      ← restriction_naturality, ← Category.assoc]
  · simp only [TupleRestrictionFunctor.rowBasis, dite_eq_right h, comp_zero, zero_comp]

theorem row_naturality {n m : ℕ} (a : Fin (n+1) → ι) (x : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m) :
    (componentIso r U P m).hom ≫ TupleRestrictionFunctor.row (r.obj ∘ U) P a x =
      TupleRestrictionFunctor.row U (r.op ⋙ P) a x ≫ (factorIso r U P a).hom := by
  classical
  simp only [TupleRestrictionFunctor.row, Finsupp.lsum_apply, Finsupp.sum, LinearMap.toSpanSingleton_apply,
    comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  intro b hb
  rw [rowBasis_naturality]

theorem map_naturality {n m : ℕ} (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains.CechTupleChain ι m)
    (ha : AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing a) :
    (componentIso r U P m).hom ≫ TupleRestrictionFunctor.map (r.obj ∘ U) P a ha =
      TupleRestrictionFunctor.map U (r.op ⋙ P) a ha ≫ (componentIso r U P n).hom := by
  apply Pi.hom_ext
  intro b
  change ((componentIso r U P m).hom ≫ TupleRestrictionFunctor.map (r.obj ∘ U) P a ha) ≫
      TupleRestrictionFunctor.projection (r.obj ∘ U) P b =
    (TupleRestrictionFunctor.map U (r.op ⋙ P) a ha ≫ (componentIso r U P n).hom) ≫
      TupleRestrictionFunctor.projection (r.obj ∘ U) P b
  rw [Category.assoc, TupleRestrictionFunctor.map_projection, Category.assoc, component_projection,
    ← Category.assoc, TupleRestrictionFunctor.map_projection]
  exact row_naturality r U P b (a (Finsupp.single b 1))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleReindex
