import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexFamilyTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCover

/-! # Reindex Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexGlobal

noncomputable section

/-! The original global common-cover map is compatible with inverse
image of a relative cover, using its literal distinguished-chart family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
attribute [local instance] ReindexData.preimage_limits
variable {κ μ ρ : Type u} [LinearOrder κ] [LinearOrder μ] [LinearOrder ρ]
  (U : Opens X) (B : κ → Opens X) (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ) (Intersections.cover U B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)

def leftRefinement : FormalCoproduct.mk ρ ((ReindexData.preimage f).obj ∘ T) ⟶
    FormalCoproduct.mk (WithBot κ)
      (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ B)) :=
  OrderedCech.ReindexFamilyRefinement.familyRefinement (ReindexData.preimage f) (Intersections.cover U B) T l
    (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ B))
    ((ReindexData.preimage f).obj ∘ T) (ReindexData.cover_eq f U B) rfl

abbrev rightRefinement := Cech.BaseChangeRefinement.refinement (ReindexData.preimage f) V T t

omit [LinearOrder μ] [LinearOrder ρ] in
theorem right_eq :
    OrderedCech.ReindexFamilyRefinement.familyRefinement (ReindexData.preimage f) V T t
      ((ReindexData.preimage f).obj ∘ V) ((ReindexData.preimage f).obj ∘ T) rfl rfl = rightRefinement f V T t := by
  simp only [OrderedCech.ReindexFamilyRefinement.familyRefinement, eqToHom_refl,
    Category.id_comp, Category.comp_id, rightRefinement]

variable {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ A) ℕ) (q : ℕ)

theorem target_total_coordinates : ReindexTotal.targetTotalIso f U B K =
    OrderedCech.ReindexFamilyTotal.familyTotalIso (ReindexData.preimage f) (Intersections.cover U B)
      (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ B))
      (ReindexData.cover_eq f U B) K := rfl

variable [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (ReindexTotal.pushed f K)) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap ((ReindexData.preimage f).obj ∘ V)
    ((ReindexData.preimage f).obj ∘ T) (rightRefinement f V T t) K) q)]

theorem global_comparison :
    Presheaf.OrderedCover.Comparison.comparison (Intersections.cover U B)
        V T l t (ReindexTotal.pushed f K) q ≫
      homologyMap (OrderedCech.ReindexTotal.totalIso (ReindexData.preimage f) V K).hom q =
    homologyMap (ReindexTotal.targetTotalIso f U B K).hom q ≫
      Presheaf.OrderedCover.Comparison.comparison
        (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ B))
        ((ReindexData.preimage f).obj ∘ V) ((ReindexData.preimage f).obj ∘ T)
        (leftRefinement f U B T l) (rightRefinement f V T t) K q := by
  let : IsIso (homologyMap (OrderedCech.Refinement.totalMap ((ReindexData.preimage f).obj ∘ V)
      ((ReindexData.preimage f).obj ∘ T)
      (OrderedCech.ReindexFamilyRefinement.familyRefinement (ReindexData.preimage f) V T t
        ((ReindexData.preimage f).obj ∘ V) ((ReindexData.preimage f).obj ∘ T) rfl rfl) K) q) := by
    rw [right_eq]
    infer_instance
  have h := OrderedCech.ReindexFamilyTotal.family_comparison (ReindexData.preimage f)
    (Intersections.cover U B) V T l t
    (Intersections.cover ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ B))
    ((ReindexData.preimage f).obj ∘ V) ((ReindexData.preimage f).obj ∘ T) (ReindexData.cover_eq f U B) rfl rfl K q
  simpa only [OrderedCech.ReindexFamilyTotal.familyTotalIso_refl, right_eq,
    Presheaf.OrderedCover.Comparison.comparison, target_total_coordinates, leftRefinement] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexGlobal
