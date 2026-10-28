import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDecomposition
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockSchemeTower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Block Retraction -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction

noncomputable section

/-! Each coefficient block is an actual scheme retract of the full
torsion scheme, via its integral projector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

theorem iso_conjugated_retraction
    {C : Type*} [Category C] {X Y B G : C}
    (eB : X ≅ B) (eG : Y ≅ G) (i : B ⟶ G) (r : G ⟶ B) (h : i ≫ r = 𝟙 B) :
    (eB.hom ≫ i ≫ eG.inv) ≫ (eG.hom ≫ r ≫ eB.inv) = 𝟙 X := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc i r, h, Category.id_comp, Iso.hom_inv_id]

variable {S : Scheme} {g : ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def torsionProjectionNat (n : ℕ) (τ : Gal(E/ℚ)) :
    A.torsionFunctor (q ^ n) ⟶ BlocksProjectors.blockFunctor A ρ (j.localCharacter iota τ) n where
  app T := GrpCat.ofHom (BlockDecomposition.torsionProjection j iota hsplit A ρ n τ T.unop)
  naturality _ _ _ := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc _ _ _)

theorem blockInclusion_projection (n : ℕ) (τ : Gal(E/ℚ)) :
    BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n ≫ torsionProjectionNat j iota hsplit A ρ n τ =
      𝟙 (BlocksProjectors.blockFunctor A ρ (j.localCharacter iota τ) n) := by
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  exact Subtype.ext (BlockDecomposition.block_projector_self j iota hsplit A ρ n τ T.unop x)

abbrev actualTorsionGroup (n : ℕ) : Grp (Over S) := ⟨A.torsionScheme (q ^ n)⟩

def blockToTorsionGroup (n : ℕ) (τ : Gal(E/ℚ)) :
    (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ⟶ actualTorsionGroup (q := q) A n :=
  yonedaGrpFullyFaithful.preimage
    ((BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ).hom ≫
      BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n ≫ (A.torsionSchemeYonedaIso (q ^ n)).inv)

def torsionToBlockGroup (n : ℕ) (τ : Gal(E/ℚ)) :
    actualTorsionGroup (q := q) A n ⟶ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp :=
  yonedaGrpFullyFaithful.preimage
    ((A.torsionSchemeYonedaIso (q ^ n)).hom ≫ torsionProjectionNat j iota hsplit A ρ n τ ≫
      (BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ).inv)

theorem block_group_retraction (n : ℕ) (τ : Gal(E/ℚ)) :
    blockToTorsionGroup j iota hsplit A ρ n τ ≫ torsionToBlockGroup j iota hsplit A ρ n τ = 𝟙 _ := by
  apply yonedaGrp.map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  dsimp only [blockToTorsionGroup, torsionToBlockGroup]
  rw [yonedaGrpFullyFaithful.map_preimage, yonedaGrpFullyFaithful.map_preimage]
  exact iso_conjugated_retraction (BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ)
    (A.torsionSchemeYonedaIso (q ^ n)) _ _ (blockInclusion_projection j iota hsplit A ρ n τ)

theorem block_scheme_retraction (n : ℕ) (τ : Gal(E/ℚ)) :
    (blockToTorsionGroup j iota hsplit A ρ n τ).hom.hom ≫
      (torsionToBlockGroup j iota hsplit A ρ n τ).hom.hom = 𝟙 _ :=
  congrArg (fun f => (Grp.forget (Over S)).map f) (block_group_retraction j iota hsplit A ρ n τ)

theorem blockToTorsionGroup_inclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    (blockToTorsionGroup j iota hsplit A ρ n τ).hom.hom ≫ A.torsionInclusion (q ^ n) =
      BlockSchemeTower.blockSchemeInclusion j iota hsplit A ρ n τ := by
  have h := yonedaGrpFullyFaithful.map_preimage
    (X := (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp)
    (Y := actualTorsionGroup (q := q) A n)
    ((BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ).hom ≫
      BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n ≫ (A.torsionSchemeYonedaIso (q ^ n)).inv)
  have hcancel :
      ((BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ).hom ≫
        BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n ≫ (A.torsionSchemeYonedaIso (q ^ n)).inv) ≫
          (A.torsionSchemeYonedaIso (q ^ n)).hom =
        (BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ).hom ≫ BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hc := (congrArg (fun α => α ≫ (A.torsionSchemeYonedaIso (q ^ n)).hom) h).trans hcancel
  have hx := congrArg (fun α =>
    ((α.app (op (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X)).hom (𝟙 _)).val) hc
  change ((𝟙 _) ≫ (blockToTorsionGroup j iota hsplit A ρ n τ).hom.hom) ≫
    A.torsionInclusion (q ^ n) = (𝟙 _) ≫ BlockSchemeTower.blockSchemeInclusion j iota hsplit A ρ n τ at hx
  simpa only [Category.id_comp] using hx

instance blockToTorsionGroup_closed (n : ℕ) (τ : Gal(E/ℚ)) :
    IsClosedImmersion (blockToTorsionGroup j iota hsplit A ρ n τ).hom.hom.left := by
  let : IsClosedImmersion (A.torsionInclusion (q ^ n)).left :=
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionInclusion_closedImmersion A (q ^ n)
  have h := congrArg Over.Hom.left (blockToTorsionGroup_inclusion j iota hsplit A ρ n τ)
  have : IsClosedImmersion
      ((blockToTorsionGroup j iota hsplit A ρ n τ).hom.hom.left ≫ (A.torsionInclusion (q ^ n)).left) :=
    (congrArg IsClosedImmersion h).mpr (BlocksProjectors.idempotentBlockInclusion_closed A ρ _ _)
  exact IsClosedImmersion.of_comp _ (A.torsionInclusion (q ^ n)).left

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction
