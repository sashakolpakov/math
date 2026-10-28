import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.OverMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle

/-! # Embedding Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EmbeddingProducts

noncomputable section

/-! Products of embeddings defined by sections use the actual tensor
product sections, and the native product presentation pulls O(1) back to
the external tensor product of the source line bundles. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {X Y : Over S} (L : Line.Bundles.LineBundle X.left) (M : Line.Bundles.LineBundle Y.left)
variable {n m : ℕ}
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ L.sheaf))
variable (t : Fin (m + 1) → (Line.Bundles.structureModule Y.left ⟶ M.sheaf))
variable (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (ht : ∀ y : Y.left, ∃ j, y ∈ Ample.LineBundles.sectionNonvanishing (t j))

def externalPairSectionFamily (i : Fin (Affine.SegreOver.segreProjectiveDimension.{u} n m + 1)) :
    Line.Bundles.structureModule (X ⊗ Y).left ⟶ (Graph.ExternalTensorBundle.externalTensorBundle L M).sheaf :=
  Tensor.PairSectionFrames.tensorPairSectionFamily (L.pullback (fst X Y).left) (M.pullback (snd X Y).left)
    (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m))
    (fun j => Ample.LineBundles.pullbackSection (fst X Y).left (s j))
    (fun j => Ample.LineBundles.pullbackSection (snd X Y).left (t j)) i

include hs ht in
theorem externalPairSectionFamily_covers :
    ∀ x : (X ⊗ Y).left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (externalPairSectionFamily L M s t i) :=
  Tensor.PairSectionFrames.tensorPairSectionFamily_covers _ _ _ _ _
    (ChartArbitraryPullback.lineBundleSections_pullback_covers (fst X Y).left L s hs)
    (ChartArbitraryPullback.lineBundleSections_pullback_covers (snd X Y).left M t ht)

private theorem tensorHom_comp_eq {S : Scheme.{u}}
    {X Y A B T : Over S} (a : X ⟶ A) (b : Y ⟶ B) (c : X ⊗ Y ⟶ A) (d : X ⊗ Y ⟶ B)
    (e : A ⊗ B ⟶ T) (r : X ⊗ Y ⟶ T)
    (ha : fst X Y ≫ a = c) (hb : snd X Y ≫ b = d) (hr : lift c d ≫ e = r) :
    (a ⊗ₘ b) ≫ e = r := by
  have h : a ⊗ₘ b = lift c d := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [tensorHom_fst, lift_fst, ha]
    · rw [tensorHom_snd, lift_snd, hb]
  exact (congrArg (fun f => f ≫ e) h).trans hr

abbrev tensorSectionProjectiveMorphism_segre := by
  have ha := OverMaps.sectionProjectiveOverMap_precomp (fst X Y) L s hs
    (ChartArbitraryPullback.lineBundleSections_pullback_covers (fst X Y).left L s hs)
  have hb := OverMaps.sectionProjectiveOverMap_precomp (snd X Y) M t ht
    (ChartArbitraryPullback.lineBundleSections_pullback_covers (snd X Y).left M t ht)
  have hr := OverMaps.sectionProjectiveOverMap_pair_segre (X ⊗ Y)
    (L.pullback (fst X Y).left) (M.pullback (snd X Y).left)
    (fun i => Ample.LineBundles.pullbackSection (fst X Y).left (s i))
    (fun i => Ample.LineBundles.pullbackSection (snd X Y).left (t i))
    (ChartArbitraryPullback.lineBundleSections_pullback_covers (fst X Y).left L s hs)
    (ChartArbitraryPullback.lineBundleSections_pullback_covers (snd X Y).left M t ht)
  exact tensorHom_comp_eq (OverMaps.sectionProjectiveOverMap X s hs) (OverMaps.sectionProjectiveOverMap Y t ht)
    _ _ _ _ ha hb hr

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EmbeddingProducts
