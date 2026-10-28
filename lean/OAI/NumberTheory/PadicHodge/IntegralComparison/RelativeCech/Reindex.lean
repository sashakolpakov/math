import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PresheafCommonRefinement

/-! # Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Reindex

noncomputable section

/-! The original relative common-cover comparison commutes with
inverse image, including the inverse refinement and signed extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (b : A ⟶ B) (c : D ⟶ E) (u : A ⟶ D) (v : B ⟶ E) [IsIso b] [IsIso c]
    (h : b ≫ v = u ≫ c) : inv b ≫ u = v ≫ inv c := by
  apply (cancel_mono c).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

private theorem paste {C : Type*} [Category C] {X Y Z T X' Y' Z' T' : C}
    (a : X ⟶ Y) (b : Z ⟶ Y) (c : Z ⟶ T)
    (a' : X' ⟶ Y') (b' : Z' ⟶ Y') (c' : Z' ⟶ T')
    (eX : X ⟶ X') (eY : Y ⟶ Y') (eZ : Z ⟶ Z') (eT : T ⟶ T')
    [IsIso b] [IsIso b']
    (h₁ : a ≫ eY = eX ≫ a') (h₂ : b ≫ eY = eZ ≫ b') (h₃ : c ≫ eT = eZ ≫ c') :
    (a ≫ inv b ≫ c) ≫ eT = eX ≫ a' ≫ inv b' ≫ c' := by
  have hi := inverse_square b b' eZ eY h₂
  simp only [Category.assoc]
  rw [h₃, ← Category.assoc (inv b) eZ c', hi]
  simp only [Category.assoc]
  rw [← Category.assoc a eY (inv b' ≫ c'), h₁]
  simp only [Category.assoc]

universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
attribute [local instance] ReindexData.preimage_limits
variable (U : Opens X) {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → Opens X) (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι V)
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ A) ℕ) (q : ℕ)

abbrev mapped {α β : Type u} (V : α → Opens X) (W : β → Opens X)
    (r : FormalCoproduct.mk β W ⟶ FormalCoproduct.mk α V) :=
  Cech.BaseChangeRefinement.refinement (ReindexData.preimage f) V W r

theorem homology_extension :
    homologyMap (Total.map U V (ReindexTotal.pushed f K)) q ≫
      homologyMap (ReindexTotal.targetTotalIso f U V K).hom q =
    homologyMap (ReindexTotal.sourceTotalIso f U V K).hom q ≫
      homologyMap (Total.map ((ReindexData.preimage f).obj U) ((ReindexData.preimage f).obj ∘ V) K) q := by
  simpa only [homologyMap_comp] using congrArg (fun a => homologyMap a q) (ReindexTotal.total_extension f U V K)

theorem homology_refinement :
    Refinement.homology U V J r (ReindexTotal.pushed f K) q ≫
      homologyMap (ReindexTotal.sourceTotalIso f U J K).hom q =
    homologyMap (ReindexTotal.sourceTotalIso f U V K).hom q ≫
      Refinement.homology ((ReindexData.preimage f).obj U)
        ((ReindexData.preimage f).obj ∘ V) ((ReindexData.preimage f).obj ∘ J) (mapped f V J r) K q := by
  simpa only [Refinement.homology, homologyMap_comp] using
    congrArg (fun a => homologyMap a q) (ReindexTotal.total_refinement f U V K J r)

variable [IsIso (Refinement.homology U B J s (ReindexTotal.pushed f K) q)]
  [IsIso (Refinement.homology ((ReindexData.preimage f).obj U)
    ((ReindexData.preimage f).obj ∘ B) ((ReindexData.preimage f).obj ∘ J) (mapped f B J s) K q)]

theorem comparison :
    Relative.PresheafCommonRefinement.comparison U V B J r s (ReindexTotal.pushed f K) q ≫
      homologyMap (ReindexTotal.targetTotalIso f U B K).hom q =
    homologyMap (ReindexTotal.sourceTotalIso f U V K).hom q ≫
      Relative.PresheafCommonRefinement.comparison ((ReindexData.preimage f).obj U)
        ((ReindexData.preimage f).obj ∘ V) ((ReindexData.preimage f).obj ∘ B) ((ReindexData.preimage f).obj ∘ J)
        (mapped f V J r) (mapped f B J s) K q :=
  paste _ _ _ _ _ _ _ _ _ _
    (homology_refinement f U V J r K q)
    (homology_refinement f U B J s K q)
    (homology_extension f U B K q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Reindex
