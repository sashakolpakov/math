import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomCupSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceCompactPushforward
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace

/-! # Proper Compact Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ProperCompactSupport.Constructions.Construction

noncomputable section

/-! The exact image of an actual compact preimage is the intersection with the regular cycle support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

abbrev regularCompactPreimage (K : Compacts Z.regularAmbientSpace) :=
  AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K

def regularAmbientCompactComplement (K : Compacts Z.regularAmbientSpace) : Opens Z.regularAmbientSpace :=
  ⟨(K : Set Z.regularAmbientSpace)ᶜ, K.isCompact.isClosed.isOpen_compl⟩

theorem regularCompactPreimage_image (K : Compacts Z.regularAmbientSpace) :
    HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) (regularCompactPreimage Z K) =
      HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) Z.regularThomComplementOpen.isOpen K := by
  apply Compacts.ext
  change Z.regularComplementInclusion '' (Z.regularComplementInclusion ⁻¹' (K : Set Z.regularAmbientSpace)) =
    (K : Set Z.regularAmbientSpace) ∩ (Set.range Z.regularComplementInclusion)ᶜᶜ
  rw [compl_compl]
  exact Set.image_preimage_eq_inter_range

theorem regularCompactPreimage_sourceComplement (K : Compacts Z.regularAmbientSpace) :
    (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj (regularAmbientCompactComplement Z K) :
      Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) =
      (regularCompactPreimage Z K : Set Z.regularAnalyticSpace)ᶜ := rfl

theorem regularCompactPreimage_targetComplement (K : Compacts Z.regularAmbientSpace) :
    ((Z.regularThomComplementOpen ⊔ regularAmbientCompactComplement Z K : Opens Z.regularAmbientSpace) :
      Set Z.regularAmbientSpace) =
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) (regularCompactPreimage Z K) : Set Z.regularAmbientSpace)ᶜ :=
  (HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection_complement (TopCat.of Z.regularAmbientSpace)
    (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) Z.regularThomComplementOpen.isOpen K).trans
      (congrArg (fun L : Compacts Z.regularAmbientSpace => (L : Set Z.regularAmbientSpace)ᶜ)
        (regularCompactPreimage_image Z K).symm)

theorem regularAmbientCompactComplement_le_preimageImage (K : Compacts Z.regularAmbientSpace) :
    regularAmbientCompactComplement Z K ≤ SupportedThomSource.Constructions.Construction.regularCompactImageComplement Z (regularCompactPreimage Z K) := by
  intro y hy
  change y ∉ (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) '' (regularCompactPreimage Z K : Set Z.regularAnalyticSpace)
  rintro ⟨x, hx, rfl⟩
  exact hy hx

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ProperCompactSupport.Constructions.Construction
