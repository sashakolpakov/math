import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision
import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

/-! # Open Embedding Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions

noncomputable section

section

/-!
# DegreeTwo: actual closed-support excision along an open embedding

Factor the literal map through its open range and its genuine range
homeomorphism. The resulting isomorphism is the original relative pullback.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)

def openEmbeddingSupportCohomologyIso (K : Set Y) (hK : IsClosed K)
    (hKr : K ⊆ Set.range f) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y Kᶜ n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (f ⁻¹' K)ᶜ n :=
  CycleClass.Geometric.RelativeCohomologyExcision.Cycles.closedSupportCohomologyIso Y (Set.range f) K hK hf.isOpen_range hKr n ≪≫
    AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
      (X := X) (Y := TopCat.of (Set.range f)) hf.toIsEmbedding.toHomeomorph
      (f ⁻¹' K)ᶜ ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y (Set.range f)) ⁻¹' K)ᶜ (fun _ => Iff.rfl) n

theorem openEmbeddingSupportCohomologyIso_hom (K : Set Y) (hK : IsClosed K)
    (hKr : K ⊆ Set.range f) (n : ℕ) :
    (openEmbeddingSupportCohomologyIso f hf K hK hKr n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx) n := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y (Set.range f))
      (A := ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y (Set.range f)) ⁻¹' K)ᶜ) (B := Kᶜ)
      (fun _ hx => hx) n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.isoOfHomeo (X := X) (Y := TopCat.of (Set.range f))
        hf.toIsEmbedding.toHomeomorph).hom
      (A := (f ⁻¹' K)ᶜ) (B := ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y (Set.range f)) ⁻¹' K)ᶜ)
      (fun _ hx => hx) n = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

include hf in
theorem openEmbedding_image_complement (K : Set X) :
    (f ⁻¹' (f '' K))ᶜ = Kᶜ := by
  rw [Set.preimage_image_eq K hf.injective]

include hf in
theorem openEmbedding_mapsTo_image_complement (K : Set X) :
    Set.MapsTo f Kᶜ (f '' K)ᶜ := by
  intro x hx
  rintro ⟨y,hy,hyx⟩
  exact hx (hf.injective hyx ▸ hy)

def openEmbeddingImageSupportCohomologyIso (K : Set X) (hK : IsClosed (f '' K)) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (f '' K)ᶜ n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ n :=
  openEmbeddingSupportCohomologyIso f hf (f '' K) hK (Set.image_subset_range f K) n ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n)
      (openEmbedding_image_complement f hf K))

theorem relativeCohomologyMap_codomainComplementCast {A A' : Set X} {B : Set Y}
    (h : A = A') (hm : Set.MapsTo f A B) (hm' : Set.MapsTo f A' B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm n ≫
      eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) h) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm' n := by
  subst A'
  exact Category.comp_id _

theorem openEmbeddingImageSupportCohomologyIso_hom (K : Set X) (hK : IsClosed (f '' K)) (n : ℕ) :
    (openEmbeddingImageSupportCohomologyIso f hf K hK n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (openEmbedding_mapsTo_image_complement f hf K) n := by
  rw [openEmbeddingImageSupportCohomologyIso, Iso.trans_hom,
    openEmbeddingSupportCohomologyIso_hom]
  exact relativeCohomologyMap_codomainComplementCast f
    (openEmbedding_image_complement f hf K) _ _ n

end

section

/-! Extension of actual compact-support classes along an actual open embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)

def embeddingCompactImage (K : Compacts X) : Compacts Y :=
  ⟨f '' (K : Set X), K.isCompact.image f.hom.continuous⟩

theorem embeddingCompactImage_mono {K L : Compacts X} (h : K ≤ L) :
    embeddingCompactImage f K ≤ embeddingCompactImage f L := Set.image_mono h

variable [T2Space Y]

def openEmbeddingCompactStageIso (K : Compacts X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (embeddingCompactImage f K : Set Y)ᶜ n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ n :=
  openEmbeddingImageSupportCohomologyIso f hf K (embeddingCompactImage f K).isCompact.isClosed n

theorem openEmbeddingCompactStageIso_hom (K : Compacts X) (n : ℕ) :
    (openEmbeddingCompactStageIso f hf K n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (openEmbedding_mapsTo_image_complement f hf K) n :=
  openEmbeddingImageSupportCohomologyIso_hom f hf K _ n

theorem openEmbeddingCompactStageIso_naturality {K L : Compacts X} (h : K ≤ L) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) (embeddingCompactImage_mono f h) n ≫
      (openEmbeddingCompactStageIso f hf L n).hom =
    (openEmbeddingCompactStageIso f hf K n).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h n := by
  rw [openEmbeddingCompactStageIso_hom, openEmbeddingCompactStageIso_hom]
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Y)
      (A := (embeddingCompactImage f L : Set Y)ᶜ) (B := (embeddingCompactImage f K : Set Y)ᶜ)
      (fun _ hx hy => hx (embeddingCompactImage_mono f h hy)) n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
      (openEmbedding_mapsTo_image_complement f hf L) n =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
      (openEmbedding_mapsTo_image_complement f hf K) n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X)
      (A := (L : Set X)ᶜ) (B := (K : Set X)ᶜ) (fun _ hx hy => hx (h hy)) n
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  simp only [Category.comp_id, Category.id_comp]

theorem openEmbeddingCompactStageIso_inv_naturality {K L : Compacts X} (h : K ≤ L) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h n ≫
      (openEmbeddingCompactStageIso f hf L n).inv =
    (openEmbeddingCompactStageIso f hf K n).inv ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) (embeddingCompactImage_mono f h) n := by
  apply (cancel_mono (openEmbeddingCompactStageIso f hf L n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    openEmbeddingCompactStageIso_naturality, Iso.inv_hom_id_assoc]

def openEmbeddingCompactExtension (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y n :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) X n
    (fun K => (openEmbeddingCompactStageIso f hf K n).inv ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y (embeddingCompactImage f K) n)
    (fun K L h => by
      rw [← Category.assoc, openEmbeddingCompactStageIso_inv_naturality,
        Category.assoc, AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι])

theorem compactSupportCohomologyι_embeddingExtension (K : Compacts X) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n ≫ openEmbeddingCompactExtension f hf n =
      (openEmbeddingCompactStageIso f hf K n).inv ≫
        AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y (embeddingCompactImage f K) n :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) X n _ _ K

end

/-! Open extension of an actual relative pullback recovers its supported class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} [T2Space Y] (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)

theorem openEmbeddingCompactStageIso_pullback_inv (K : Compacts X) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
      (openEmbedding_mapsTo_image_complement f hf K) n
      ((openEmbeddingCompactStageIso f hf K n).inv a) = a := by
  rw [← openEmbeddingCompactStageIso_hom f hf K n]
  exact (openEmbeddingCompactStageIso f hf K n).inv_hom_id_apply a

theorem openEmbeddingCompactExtension_stage (K : Compacts X) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ n) :
    openEmbeddingCompactExtension f hf n
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n a) =
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y (embeddingCompactImage f K) n
        ((openEmbeddingCompactStageIso f hf K n).inv a) :=
  ConcreteCategory.congr_hom (compactSupportCohomologyι_embeddingExtension f hf K n) a

theorem openEmbeddingCompactExtension_pullback (K : Compacts X) (L : Compacts Y)
    (hL : f '' (K : Set X) = (L : Set Y))
    (hm : Set.MapsTo f (K : Set X)ᶜ (L : Set Y)ᶜ) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ n) :
    openEmbeddingCompactExtension f hf n
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm n a)) =
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y L n a := by
  have he : embeddingCompactImage f K = L := Compacts.ext hL
  subst L
  rw [openEmbeddingCompactExtension_stage]
  change AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y (embeddingCompactImage f K) n
    ((openEmbeddingCompactStageIso f hf K n).inv
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (openEmbedding_mapsTo_image_complement f hf K) n a)) = _
  rw [← openEmbeddingCompactStageIso_hom f hf K n]
  exact congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y (embeddingCompactImage f K) n)
    ((openEmbeddingCompactStageIso f hf K n).hom_inv_id_apply a)

theorem openEmbeddingCompactExtension_openSubspace {Y : TopCat.{0}} [T2Space Y]
    (U : Opens Y) (n : ℕ) :
    openEmbeddingCompactExtension (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y U) U.isOpen.isOpenEmbedding_subtypeVal n =
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension U n := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of U) n
  intro K
  rw [compactSupportCohomologyι_embeddingExtension, AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportCohomologyι_openExtension]
  have he : openEmbeddingCompactStageIso (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y U)
      U.isOpen.isOpenEmbedding_subtypeVal K n = AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso U K n := by
    apply Iso.ext
    rw [openEmbeddingCompactStageIso_hom]
    rfl
  rw [he]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions
