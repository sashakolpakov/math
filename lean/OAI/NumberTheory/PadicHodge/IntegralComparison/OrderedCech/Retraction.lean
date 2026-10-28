import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Projection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SortedProjection

/-! # Retraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Retraction

noncomputable section

/-! Ordered Čech cochains are a split cochain retract of the original
all-tuples cochains. Only finite signed sorting is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (P : Cᵒᵖ ⥤ D)

open OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Projection

theorem sorted_mapF (n : ℕ) :
    Cech.SortedProjection.component U P n ≫ Projection.mapF U P n = Projection.mapF U P n := by
  apply Pi.hom_ext
  intro (a : Projection.Index (ι := ι) n)
  change _ ≫ Projection.projection U P n a = _ ≫ Projection.projection U P n a
  rw [Category.assoc, Projection.mapF_projection,
    Cech.SortedProjection.projection_strictMono U P n a.val a.property]

theorem projection_zero_sorted (n : ℕ) :
    (Projection.mapF U P n ≫ Projection.zeroExtension U P n) ≫ Cech.SortedProjection.component U P n =
      Cech.SortedProjection.component U P n := by
  apply Pi.hom_ext
  intro (a : Fin (n + 1) → ι)
  change _ ≫ Cech.TupleRestrictionFunctor.projection U P a =
    _ ≫ Cech.TupleRestrictionFunctor.projection U P a
  rw [Category.assoc]
  by_cases ha : Function.Injective a
  · rw [Cech.SortedProjection.projection_injective U P n a ha, comp_zsmul]
    have hs : StrictMono (a ∘ Tuple.sort a) :=
      (Tuple.monotone_sort a).strictMono_of_injective (ha.comp (Tuple.sort a).injective)
    have hr : Set.range (a ∘ Tuple.sort a) ⊆ Set.range a := by
      rintro x ⟨i, rfl⟩
      exact ⟨Tuple.sort a i, rfl⟩
    rw [Cech.TupleRestrictionFunctor.rowBasis_of_subset U P a _ hr,
      ← Category.assoc, Category.assoc (Projection.mapF U P n),
      Projection.zeroExtension_projection U P n _ hs, Projection.mapF_projection]
  · rw [Cech.SortedProjection.projection_not_injective U P n a ha, comp_zero]

def inclusionF (n : ℕ) : Projection.object U P n ⟶ (Cech.TupleRestrictionFunctor.complex U P).X n :=
  Projection.zeroExtension U P n ≫ Cech.SortedProjection.component U P n

theorem mapF_inclusionF (n : ℕ) : Projection.mapF U P n ≫ inclusionF U P n =
    Cech.SortedProjection.component U P n := by
  exact (Category.assoc _ _ _).symm.trans (projection_zero_sorted U P n)

theorem inclusionF_mapF (n : ℕ) : inclusionF U P n ≫ Projection.mapF U P n = 𝟙 _ := by
  erw [inclusionF, Category.assoc, sorted_mapF, Projection.zeroExtension_mapF]

theorem inclusionF_d (n : ℕ) :
    inclusionF U P n ≫ (Cech.TupleRestrictionFunctor.complex U P).d n (n + 1) =
      (Projection.complex U P).d n (n + 1) ≫ inclusionF U P (n + 1) := by
  apply (cancel_epi (Projection.mapF U P n)).mp
  erw [← Category.assoc, mapF_inclusionF, Cech.SortedProjection.comm]
  erw [show (Projection.complex U P).d n (n + 1) = Projection.differential U P n from CochainComplex.of_d _ _ n,
    ← Category.assoc, Projection.mapF_d, Category.assoc, mapF_inclusionF]

def inclusion : Projection.complex U P ⟶ Cech.TupleRestrictionFunctor.complex U P :=
  CochainComplex.ofHom (inclusionF U P) (inclusionF_d U P)

theorem inclusion_map : inclusion U P ≫ Projection.map U P = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  exact inclusionF_mapF U P n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Retraction
