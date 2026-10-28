import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocalDescent
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedComparison

/-! # Product Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ProductLineDescent

noncomputable section

/-! Target-normalized comparisons descend on products of abelian
varieties through the actual finite etale quotient map. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

namespace Construction

theorem tensor_left_isPullback {S : Scheme.{0}} (H : Over S) {A B : Over S} (f : A ⟶ B) :
    IsPullback (snd H A) (𝟙 H ⊗ₘ f) f (snd H B) := by
  apply IsPullback.mk' (by simp)
  · intro T p q hs ht
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (· ≫ fst H B) ht
      simpa only [Category.assoc, tensorHom_fst, Category.comp_id] using h
    · exact hs
  · intro T a b hab
    refine ⟨lift (b ≫ fst H B) a, by simp, ?_⟩
    apply CartesianMonoidalCategory.hom_ext <;> simp [hab]

theorem tensor_left_quotient_geometry {S : Scheme.{0}} (H : Over S) {A B : Over S}
    (f : A ⟶ B) [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    IsFinite (𝟙 H ⊗ₘ f).left ∧ Etale (𝟙 H ⊗ₘ f).left ∧ Surjective (𝟙 H ⊗ₘ f).left := by
  have h := (Over.forget S).map_isPullback (tensor_left_isPullback H f)
  exact ⟨MorphismProperty.of_isPullback h ‹IsFinite f.left›,
    MorphismProperty.of_isPullback h ‹Etale f.left›,
    MorphismProperty.of_isPullback h ‹Surjective f.left›⟩

theorem normalized_product_line_iso
    {k : Type} [Field k] [IsAlgClosed k] {g h j : ℕ}
    (H : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme j (Spec (.of k))) (f : A.scheme ⟶ B.scheme)
    [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (H.scheme ⊗ B.scheme).left)
    (hLM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 H.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 H.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
    (l : (L.pullback (lift (1 : B.scheme ⟶ H.scheme) (𝟙 B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left)
    (m : (M.pullback (lift (1 : B.scheme ⟶ H.scheme) (𝟙 B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left) : Nonempty (L.sheaf ≅ M.sheaf) := by
  obtain ⟨hf, he, hs⟩ := tensor_left_quotient_geometry H.scheme f
  obtain ⟨a, ha⟩ := NormalizedComparison.Construction.exists_normalized_product_comparison H A B f L M hLM l m
  apply LocalDescent.Construction.compatible_line_iso_desc (𝟙 H.scheme ⊗ₘ f) L M a
  intro T p q w hp hq
  subst w
  exact ha T p q hq.symm

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ProductLineDescent
