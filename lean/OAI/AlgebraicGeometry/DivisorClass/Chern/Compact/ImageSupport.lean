import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ThomIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomZero

/-! # Image Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ImageSupport

noncomputable section

/-! The compact image of the actual divisor preimage is precisely the original compact Thom support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomZero.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularCompactImage_preimage (K : Compacts D.regularAmbientSpace) :
    HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K) =
    ThomIso.regularThomCompactIntersection D K := by
  apply Compacts.ext
  change D.regularComplementInclusion '' (D.regularComplementInclusion ⁻¹' (K : Set D.regularAmbientSpace)) =
    (K : Set D.regularAmbientSpace) ∩ (Set.range D.regularComplementInclusion)ᶜᶜ
  rw [compl_compl, Set.image_preimage_eq_inter_range]

theorem compactTestComplement_le_imagePreimageComplement (K : Compacts D.regularAmbientSpace) :
    SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K ≤
      HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D
        (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K) := by
  intro y hy
  change y ∉ (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) '' (D.regularComplementTopCatMap ⁻¹' (K : Set D.regularAmbientSpace))
  rintro ⟨x, hx, rfl⟩
  exact hy hx

theorem regularCompactImagePreimage_unionComplement (K : Compacts D.regularAmbientSpace) :
    ((D.regularThomComplementOpen ⊔ SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K : Opens D.regularAmbientSpace) :
      Set D.regularAmbientSpace) =
    ((D.regularThomComplementOpen ⊔ HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K) : Opens D.regularAmbientSpace) :
      Set D.regularAmbientSpace) := by
  rw [HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement, regularCompactImage_preimage]
  exact (Set.union_comm _ _).trans (ThomIso.regularThomCompactIntersection_complement D K)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ImageSupport
