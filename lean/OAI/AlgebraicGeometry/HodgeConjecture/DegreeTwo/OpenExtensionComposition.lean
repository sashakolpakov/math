import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality

/-! # Open Extension Composition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions

noncomputable section

/-! Composition and homeomorphism laws for actual compact-support open extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : TopCat.{0}} [T2Space Y] [T2Space Z]

theorem embeddingCompactImage_comp (f : X ⟶ Y) (g : Y ⟶ Z) (K : Compacts X) :
    OpenEmbeddingExtension.Constructions.embeddingCompactImage g (OpenEmbeddingExtension.Constructions.embeddingCompactImage f K) = OpenEmbeddingExtension.Constructions.embeddingCompactImage (f ≫ g) K := by
  let _ := (inferInstance : T2Space Y)
  let _ := (inferInstance : T2Space Z)
  apply Compacts.ext
  exact Set.image_image g f (K : Set X)

theorem openEmbeddingCompactExtension_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsOpenEmbedding f) (hg : Topology.IsOpenEmbedding g) (n : ℕ) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf n ≫ OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension g hg n =
      OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (f ≫ g) (hg.comp hf) n := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) X n
  intro K
  apply (cancel_epi (OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso (f ≫ g) (hg.comp hf) K n).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  let L := OpenEmbeddingExtension.Constructions.embeddingCompactImage f K
  let T := OpenEmbeddingExtension.Constructions.embeddingCompactImage (f ≫ g) K
  have hLT : g '' (L : Set Y) = (T : Set Z) := Set.image_image g f (K : Set X)
  have hgT : Set.MapsTo g (L : Set Y)ᶜ (T : Set Z)ᶜ := by
    intro y hy h
    obtain ⟨x,hx,hxy⟩ := h
    exact hy ⟨x,hx,hg.injective hxy⟩
  have hcomp := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) f g
    (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement f hf K) hgT n
  have hpb : (OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso (f ≫ g) (hg.comp hf) K n).hom b =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement f hf K) n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hgT n b) := by
    rw [OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom]
    exact (ConcreteCategory.congr_hom hcomp b).symm
  change OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension g hg n
      (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf n
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n
          ((OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso (f ≫ g) (hg.comp hf) K n).hom b))) =
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (f ≫ g) (hg.comp hf) n
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n
        ((OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso (f ≫ g) (hg.comp hf) K n).hom b))
  have hF := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback f hf K L rfl
    (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement f hf K) n
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hgT n b)
  have hG := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback g hg L T hLT hgT n b
  have hFG := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback (f ≫ g) (hg.comp hf) K T rfl
    (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement (f ≫ g) (hg.comp hf) K) n b
  rw [← OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom (f ≫ g) (hg.comp hf) K n] at hFG
  exact (congrArg (fun a => OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension g hg n
    (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf n
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n a))) hpb).trans
    ((congrArg (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension g hg n) hF).trans (hG.trans hFG.symm))

theorem openEmbeddingCompactExtension_homeomorph (e : X ≃ₜ Y) (n : ℕ) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (TopCat.isoOfHomeo (X := X) (Y := Y) e).hom
      e.isOpenEmbedding n =
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) e n).inv := by
  apply (cancel_epi (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) e n).hom).mp
  rw [Iso.hom_inv_id]
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) Y n
  intro L
  obtain ⟨K,rfl⟩ := (Compacts.equiv e).surjective L
  rw [← Category.assoc, AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso_ι, Category.assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback
    (TopCat.isoOfHomeo (X := X) (Y := Y) e).hom e.isOpenEmbedding K
    (Compacts.equiv e K) rfl
    (fun x hx => (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactHomeomorph_complement_iff e K x).mp hx) n b

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions
