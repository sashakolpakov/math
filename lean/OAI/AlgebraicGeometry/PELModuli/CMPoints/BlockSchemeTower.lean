import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockTower

/-! # Block Scheme Tower -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockSchemeTower

noncomputable section

/-! The ascending character-block functors are represented by closed
embeddings of the actual block schemes. The Yoneda construction follows
the generic checked bridge in TorsionLevels, placed here without
the later node's Cartier and ordinary-block dependencies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def blockYonedaIso (n : ℕ) (τ : Gal(E/ℚ)) :
    yonedaGrp.obj (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ≅
      BlocksProjectors.blockFunctor A ρ (j.localCharacter iota τ) n :=
  yonedaGrpObjIsoOfRepresentableBy
    (BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ))
    (BlocksProjectors.blockFunctor A ρ (j.localCharacter iota τ) n)
    (BlocksProjectors.splitBlockRepresentable j iota hsplit A ρ n τ)

abbrev blockSchemeInclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X ⟶ A.scheme :=
  BlocksProjectors.idempotentBlockInclusion A ρ (q ^ n) (j.projector iota hsplit n τ)

theorem blockSchemeInclusion_point (n : ℕ) (τ : Gal(E/ℚ)) (T : Over S)
    (x : T ⟶ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    ((blockYonedaIso j iota hsplit A ρ n τ).hom.app (op T) x).val =
      x ≫ blockSchemeInclusion j iota hsplit A ρ n τ := rfl

def blockSchemeLevelEmbedding (τ : Gal(E/ℚ)) {n m : ℕ} (hnm : n ≤ m) :
    (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ⟶
      (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ m τ).toGrp :=
  (yonedaGrpFullyFaithful (C := Over S)).preimage
    ((blockYonedaIso j iota hsplit A ρ n τ).hom ≫
      BlockTower.blockInclusionNat A ρ (j.localCharacter iota τ) n m hnm ≫
        (blockYonedaIso j iota hsplit A ρ m τ).inv)

theorem blockSchemeLevelEmbedding_points (τ : Gal(E/ℚ)) {n m : ℕ} (hnm : n ≤ m)
    (T : Over S) (x : T ⟶ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    (blockYonedaIso j iota hsplit A ρ m τ).hom.app (op T)
      (x ≫ (blockSchemeLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom) =
        (BlockTower.blockInclusionNat A ρ (j.localCharacter iota τ) n m hnm).app (op T)
          ((blockYonedaIso j iota hsplit A ρ n τ).hom.app (op T) x) := by
  have h := (yonedaGrpFullyFaithful (C := Over S)).map_preimage
    ((blockYonedaIso j iota hsplit A ρ n τ).hom ≫
      BlockTower.blockInclusionNat A ρ (j.localCharacter iota τ) n m hnm ≫
        (blockYonedaIso j iota hsplit A ρ m τ).inv)
  have hc := congrArg (fun α => α ≫ (blockYonedaIso j iota hsplit A ρ m τ).hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  exact congrArg (fun α => (α.app (op T)).hom x) hc

theorem blockSchemeLevelEmbedding_inclusion (τ : Gal(E/ℚ)) {n m : ℕ} (hnm : n ≤ m) :
    (blockSchemeLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom ≫
      blockSchemeInclusion j iota hsplit A ρ m τ = blockSchemeInclusion j iota hsplit A ρ n τ := by
  have h := congrArg Subtype.val
    (blockSchemeLevelEmbedding_points j iota hsplit A ρ τ hnm _ (𝟙 _))
  change ((𝟙 _) ≫ (blockSchemeLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom) ≫
    blockSchemeInclusion j iota hsplit A ρ m τ =
      (𝟙 _) ≫ blockSchemeInclusion j iota hsplit A ρ n τ at h
  simpa only [Category.id_comp] using h

instance blockSchemeLevelEmbedding_closed (τ : Gal(E/ℚ)) {n m : ℕ} (hnm : n ≤ m) :
    IsClosedImmersion (blockSchemeLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom.left := by
  have : IsClosedImmersion (blockSchemeInclusion j iota hsplit A ρ m τ).left :=
    BlocksProjectors.idempotentBlockInclusion_closed A ρ _ _
  have h := congrArg Over.Hom.left
    (blockSchemeLevelEmbedding_inclusion j iota hsplit A ρ τ hnm)
  have : IsClosedImmersion
      ((blockSchemeLevelEmbedding j iota hsplit A ρ τ hnm).hom.hom.left ≫
        (blockSchemeInclusion j iota hsplit A ρ m τ).left) :=
    (congrArg IsClosedImmersion h).mpr (BlocksProjectors.idempotentBlockInclusion_closed A ρ _ _)
  exact IsClosedImmersion.of_comp _ (blockSchemeInclusion j iota hsplit A ρ m τ).left

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockSchemeTower
