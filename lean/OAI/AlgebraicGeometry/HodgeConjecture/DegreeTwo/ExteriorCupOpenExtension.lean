import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactRelativeExteriorCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension

/-! # Exterior Cup Open Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupOpenExtension.Constructions

noncomputable section

/-! The actual compact exterior cup commutes with extension along open embeddings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false

variable {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')

theorem embeddingCompactImage_prod (K : Compacts X) (L : Compacts Y) :
    OpenEmbeddingExtension.Constructions.embeddingCompactImage (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))) (K×ˢL) =
      OpenEmbeddingExtension.Constructions.embeddingCompactImage f K ×ˢ OpenEmbeddingExtension.Constructions.embeddingCompactImage g L := by
  apply Compacts.ext
  ext z
  constructor
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩
  · rintro ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
    exact ⟨(x,y),⟨hx,hy⟩,Prod.ext hxz hyz⟩

variable [T2Space X] [T2Space X'] [T2Space Y] [T2Space Y']
variable (hf : Topology.IsOpenEmbedding f) (hg : Topology.IsOpenEmbedding g)

theorem compactExteriorCupStage_extension_pullback (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X' (OpenEmbeddingExtension.Constructions.embeddingCompactImage f K : Set X')ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' (OpenEmbeddingExtension.Constructions.embeddingCompactImage g L : Set Y')ᶜ q) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (X := TopCat.of (X×Y)) (Y := TopCat.of (X'×Y')) (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
      (hf.prodMap hg) (p+q)
      (CompactExteriorCup.Constructions.compactExteriorCupStage X Y K L p q
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
          (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement f hf K) p a)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g
          (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement g hg L) q b)) =
    CompactExteriorCup.Constructions.compactExteriorCupStage X' Y' (OpenEmbeddingExtension.Constructions.embeddingCompactImage f K) (OpenEmbeddingExtension.Constructions.embeddingCompactImage g L) p q a b := by
  let fg : TopCat.of (X×Y) ⟶ TopCat.of (X'×Y') :=
    AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))
  have he : fg '' ((K×ˢL : Compacts (X×Y)) : Set (X×Y)) =
      ((OpenEmbeddingExtension.Constructions.embeddingCompactImage f K ×ˢ OpenEmbeddingExtension.Constructions.embeddingCompactImage g L : Compacts (X'×Y')) : Set (X'×Y')) :=
    congrArg (fun C : Compacts (X'×Y') => (C : Set (X'×Y'))) (embeddingCompactImage_prod f g K L)
  have hm : Set.MapsTo fg ((K×ˢL : Compacts (X×Y)) : Set (X×Y))ᶜ
      ((OpenEmbeddingExtension.Constructions.embeddingCompactImage f K ×ˢ OpenEmbeddingExtension.Constructions.embeddingCompactImage g L : Compacts (X'×Y')) : Set (X'×Y'))ᶜ := by
    rw [← he]
    exact OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement fg (hf.prodMap hg) _
  have h := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback fg (hf.prodMap hg) (K×ˢL)
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage f K ×ˢ OpenEmbeddingExtension.Constructions.embeddingCompactImage g L) he hm (p+q)
    (CompactRelativeExteriorCup.Constructions.compactRelativeExteriorCup X' Y' (OpenEmbeddingExtension.Constructions.embeddingCompactImage f K) (OpenEmbeddingExtension.Constructions.embeddingCompactImage g L) p q a b)
  have hc := CompactRelativeExteriorCup.Constructions.compactRelativeExteriorCup_naturality f g K (OpenEmbeddingExtension.Constructions.embeddingCompactImage f K)
    L (OpenEmbeddingExtension.Constructions.embeddingCompactImage g L) (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement f hf K)
    (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement g hg L) hm p q a b
  have hcc := congrArg
    (fun z : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      ((K×ˢL : Compacts (X×Y)) : Set (X×Y))ᶜ (p+q) =>
      OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension fg (hf.prodMap hg) (p+q)
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (K×ˢL) (p+q) z)) hc
  exact hcc.trans h

theorem compactExteriorCup_openExtension (p q : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y q) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (X := TopCat.of (X×Y)) (Y := TopCat.of (X'×Y')) (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
      (hf.prodMap hg) (p+q) (CompactExteriorCup.Constructions.compactExteriorCup X Y p q a b) =
    CompactExteriorCup.Constructions.compactExteriorCup X' Y' p q
      (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf p a) (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension g hg q b) := by
  obtain ⟨K,a,rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ) X p a
  obtain ⟨L,b,rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ) Y q b
  rw [CompactExteriorCup.Constructions.compactExteriorCup_stage, OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_stage,
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_stage, CompactExteriorCup.Constructions.compactExteriorCup_stage]
  have h := compactExteriorCupStage_extension_pullback f g hf hg K L p q
    ((OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso f hf K p).inv a) ((OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso g hg L q).inv b)
  have he := congrArg₂
    (fun x y => OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (X := TopCat.of (X×Y)) (Y := TopCat.of (X'×Y'))
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))) (hf.prodMap hg) (p+q)
      (CompactExteriorCup.Constructions.compactExteriorCupStage X Y K L p q x y))
    (OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_pullback_inv f hf K p a)
    (OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_pullback_inv g hg L q b)
  exact he.symm.trans h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupOpenExtension.Constructions
