import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomCupSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomZero
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace

/-! # Proper Compact Thom Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProperCompactThomSupport.Constructions

noncomputable section

/-! The exact image of an actual compact preimage is the intersection with the regular cycle support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

abbrev regularCompactPreimage (K : Compacts Z.regularAmbientSpace) :=
  AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K

def regularAmbientCompactComplement (K : Compacts Z.regularAmbientSpace) : Opens Z.regularAmbientSpace :=
  ⟨(K : Set Z.regularAmbientSpace)ᶜ, K.isCompact.isClosed.isOpen_compl⟩

theorem regularCompactPreimage_image (K : Compacts Z.regularAmbientSpace) :
    OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (regularCompactPreimage Z K) =
      CompactThomCupSupport.Constructions.thomCompactIntersection (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) Z.regularThomComplementOpen.isOpen K := by
  apply Compacts.ext
  change Z.regularComplementInclusion '' (Z.regularComplementInclusion ⁻¹' (K : Set Z.regularAmbientSpace)) =
    (K : Set Z.regularAmbientSpace) ∩ (Set.range Z.regularComplementInclusion)ᶜᶜ
  rw [compl_compl]
  exact Set.image_preimage_eq_inter_range

theorem regularCompactPreimage_sourceComplement (K : Compacts Z.regularAmbientSpace) :
    (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj (regularAmbientCompactComplement Z K) :
      Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) =
      (regularCompactPreimage Z K : Set Z.regularAnalyticSpace)ᶜ := rfl

theorem regularCompactPreimage_targetComplement (K : Compacts Z.regularAmbientSpace) :
    ((Z.regularThomComplementOpen ⊔ regularAmbientCompactComplement Z K : Opens Z.regularAmbientSpace) :
      Set Z.regularAmbientSpace) =
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (regularCompactPreimage Z K) : Set Z.regularAmbientSpace)ᶜ :=
  (CompactThomCupSupport.Constructions.thomCompactIntersection_complement (TopCat.of Z.regularAmbientSpace)
    (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) Z.regularThomComplementOpen.isOpen K).trans
      (congrArg (fun L : Compacts Z.regularAmbientSpace => (L : Set Z.regularAmbientSpace)ᶜ)
        (regularCompactPreimage_image Z K).symm)

theorem regularAmbientCompactComplement_le_preimageImage (K : Compacts Z.regularAmbientSpace) :
    regularAmbientCompactComplement Z K ≤ RegularCompactThomStage.Constructions.regularCompactImageComplement Z (regularCompactPreimage Z K) := by
  intro y hy
  change y ∉ (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) '' (regularCompactPreimage Z K : Set Z.regularAnalyticSpace)
  rintro ⟨x, hx, rfl⟩
  exact hy hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProperCompactThomSupport.Constructions
