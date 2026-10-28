import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportRepresentative

/-! # Compact Image Open Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions

noncomputable section

/-! Exact compact images commute with restricting a continuous map to the preimage of an open set. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (U : Opens X)

theorem compactImage_openPreimage_square (K : Compacts ((Opens.map f).obj U)) :
    OpenEmbeddingExtension.Constructions.embeddingCompactImage f
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y ((Opens.map f).obj U)) K) =
    OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap f U) K) := by
  apply Compacts.ext
  change f '' ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y ((Opens.map f).obj U)) '' (K : Set ((Opens.map f).obj U))) =
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) '' ((SingularSheafPullback.Constructions.openPreimageMap f U) '' (K : Set ((Opens.map f).obj U)))
  rw [Set.image_image, Set.image_image]
  rfl

theorem compactImage_openPreimage_complement (K : Compacts ((Opens.map f).obj U)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage f
        (OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y ((Opens.map f).obj U)) K) : Set X)ᶜ U =
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap f U) K : Set U)ᶜ := by
  rw [compactImage_openPreimage_square]
  change (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹'
    ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) '' (OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap f U) K : Set U))ᶜ = _
  rw [Set.preimage_compl, Set.preimage_image_eq _
    (show Function.Injective (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) from Subtype.val_injective)]

theorem compactImage_openInclusion_complement (K : Compacts U) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) K : Set X)ᶜ U = (K : Set U)ᶜ := by
  change (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) '' (K : Set U))ᶜ = _
  rw [Set.preimage_compl, Set.preimage_image_eq _
    (show Function.Injective (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) from Subtype.val_injective)]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions
