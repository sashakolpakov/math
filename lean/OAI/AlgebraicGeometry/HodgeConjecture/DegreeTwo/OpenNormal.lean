import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingPairExcision
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportedCupIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedOpenPointClass
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupNaturality

/-! # Open Normal -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenNormal.Constructions

noncomputable section

/-! The actual Thom cup isomorphism on every open neighborhood of the normal origin. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false

variable {c : ℕ} (U : Opens (Fin c → ℂ)) (h0 : (0 : Fin c → ℂ) ∈ U)
variable (Y : TopCat.{0}) (B : Set Y) (hB : IsOpen B)

abbrev normalOpenProductInclusion : TopCat.of (U×Y) ⟶ TopCat.of ((Fin c → ℂ) × Y) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin c → ℂ)) U,𝟙 Y) :
    (TopCat.of U,Y) ⟶ (TopCat.of (Fin c → ℂ),Y))

theorem normalOpenProductInclusion_isOpenEmbedding : Topology.IsOpenEmbedding (normalOpenProductInclusion U Y) :=
  U.isOpen.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id

theorem normalOpenProductComplement_preimage :
    normalOpenProductInclusion U Y ⁻¹'
      RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B =
    RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of U) Y ({⟨0,h0⟩}ᶜ) B := by
  ext z
  change ((z.1 : Fin c → ℂ) ≠ 0 ∨ z.2 ∈ B) ↔ (z.1 ≠ ⟨0,h0⟩ ∨ z.2 ∈ B)
  constructor
  · rintro (hx | hy)
    · exact Or.inl (fun h => hx (congrArg Subtype.val h))
    · exact Or.inr hy
  · rintro (hx | hy)
    · exact Or.inl (fun h => hx (Subtype.ext h))
    · exact Or.inr hy

include h0 in
theorem normalOpenProductComplement_cover :
    (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B)ᶜ ⊆
      Set.range (normalOpenProductInclusion U Y) := by
  intro z hz
  have hz0 : z.1 = 0 := by
    by_contra hn
    exact hz (Or.inl hn)
  exact ⟨(⟨0,h0⟩,z.2),Prod.ext hz0.symm rfl⟩

include hB in
theorem normalProductComplement_isOpen :
    IsOpen (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B) := by
  have hN : IsOpen ({0}ᶜ : Set (Fin c → ℂ)) := isClosed_singleton.isOpen_compl
  exact (hN.preimage continuous_fst).union (hB.preimage continuous_snd)

def openNormalProductRestrictionIso (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ((Fin c → ℂ) × Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B) q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U×Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of U) Y ({⟨0,h0⟩}ᶜ) B) q := by
  let e := OpenEmbeddingPairExcision.Constructions.openEmbeddingPairCohomologyIso (X := TopCat.of (U×Y)) (Y := TopCat.of ((Fin c → ℂ) × Y))
    (normalOpenProductInclusion U Y)
    (normalOpenProductInclusion_isOpenEmbedding U Y)
    (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of U) Y ({⟨0,h0⟩}ᶜ) B)
    (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B)
    (normalProductComplement_isOpen (c := c) Y B hB)
    (normalOpenProductComplement_preimage U h0 Y B) (normalOpenProductComplement_cover U h0 Y B) q
  exact e

def openNormalSupportedCohomologyIso (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q ≃ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U×Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of U) Y ({⟨0,h0⟩}ᶜ) B) (2*c+q) :=
  (NormalSupportedCupIso.Constructions.normalSupportedCohomologyIso c Y B hB q).trans
    (openNormalProductRestrictionIso U h0 Y B hB (2*c+q)).toLinearEquiv

theorem openNormalSupportedCohomologyIso_eq_cup (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    openNormalSupportedCohomologyIso U h0 Y B hB q a =
    ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of U) Y ({⟨0,h0⟩}ᶜ) B isClosed_singleton.isOpen_compl hB
      (2*c) q (NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0) a := by
  have hc := ExteriorCupNaturality.Constructions.relativeExteriorCup_naturality
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin c → ℂ)) U) (𝟙 Y)
    (NestedOpenPointClass.Constructions.openOrigin_mapsTo_complement U h0) (A := ({⟨0,h0⟩}ᶜ : Set U))
    (B := B) (B' := B) (fun _ hx => hx)
    isClosed_singleton.isOpen_compl hB isClosed_singleton.isOpen_compl hB
    (2*c) q (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) a
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, ModuleCat.id_apply] at hc
  unfold openNormalSupportedCohomologyIso
  rw [LinearEquiv.trans_apply, NormalSupportedCupIso.Constructions.normalSupportedCohomologyIso_eq_cup]
  change (openNormalProductRestrictionIso U h0 Y B hB (2*c+q)).hom _ = _
  rw [openNormalProductRestrictionIso, OpenEmbeddingPairExcision.Constructions.openEmbeddingPairCohomologyIso_hom]
  exact hc.symm

theorem openNormalSupportedCup_bijective (q : ℕ) :
    Function.Bijective (fun a => ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of U) Y ({⟨0,h0⟩}ᶜ) B
      isClosed_singleton.isOpen_compl hB (2*c) q (NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0) a) := by
  have he : (fun a => ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of U) Y ({⟨0,h0⟩}ᶜ) B
      isClosed_singleton.isOpen_compl hB (2*c) q (NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0) a) =
      openNormalSupportedCohomologyIso U h0 Y B hB q :=
    funext (fun a => (openNormalSupportedCohomologyIso_eq_cup U h0 Y B hB q a).symm)
  rw [he]
  exact (openNormalSupportedCohomologyIso U h0 Y B hB q).bijective

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenNormal.Constructions
