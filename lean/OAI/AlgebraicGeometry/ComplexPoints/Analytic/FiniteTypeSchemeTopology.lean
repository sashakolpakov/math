import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite Type Scheme Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology

noncomputable section

/-!
# Topology of complex points of finite-type schemes

This file derives ordinary local compactness and countability from the genuine
scheme-theoretic finite-type conditions and the actual affine open cover.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The canonical global-section algebra of an affine complex scheme locally
of finite type is a finitely generated complex algebra. -/
theorem affineOverGamma_finiteType (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : Algebra.FiniteType ℂ Γ(X.left, ⊤) := by
  rw [← RingHom.finiteType_algebraMap]
  change (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)).hom.FiniteType
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
  simpa only [Spec.map_preimage] using
    (inferInstance : LocallyOfFiniteType (X.left.isoSpec.inv ≫ X.hom))

/-- Native complex points of an affine scheme locally of finite type are
locally compact in their ordinary affine-test topology. -/
theorem affineSchemePoints_locallyCompact (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : LocallyCompactSpace (SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := affineOverGamma_finiteType X
  let : LocallyCompactSpace (SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ Γ(X.left, ⊤))) :=
    (SchemePointHomeomorphs.affineSchemePointHomeomorph Γ(X.left, ⊤)).symm.isClosedEmbedding.locallyCompactSpace
  exact (SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X)).isClosedEmbedding.locallyCompactSpace

/-- Native complex points of an affine scheme locally of finite type are
second countable, via its actual finitely generated global-section algebra. -/
theorem affineSchemePoints_secondCountable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : SecondCountableTopology (SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := affineOverGamma_finiteType X
  let : SecondCountableTopology (SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ Γ(X.left, ⊤))) :=
    (SchemePointHomeomorphs.affineSchemePointHomeomorph Γ(X.left, ⊤)).symm.isEmbedding.secondCountableTopology
  exact (SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X)).isEmbedding.secondCountableTopology

/-- The ordinary complex-point space of a scheme locally of finite type over
`ℂ` is locally compact. No separation assumption is needed for this result. -/
theorem schemePoints_locallyCompact (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] :
    LocallyCompactSpace (SchemePointHomeomorphs.schemeComplexPoints X) where
  local_compact_nhds := by
    intro p N hN
    let 𝒰 := X.left.affineCover
    obtain ⟨i, q, rfl⟩ := SchemePointHomeomorphs.schemeComplexPoints.exists_openCoverPoint_lift X 𝒰 p
    let : LocallyOfFiniteType (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝒰.f i ≫ X.hom))
    let : LocallyCompactSpace
        (SchemePointHomeomorphs.schemeComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i)) :=
      affineSchemePoints_locallyCompact (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i)
    have hf := SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_openCoverPointMap X 𝒰 i
    obtain ⟨K, hKq, hKN, hKc⟩ := local_compact_nhds (hf.continuous.continuousAt hN)
    exact ⟨SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i '' K,
      hf.isOpenMap.image_mem_nhds hKq, Set.image_subset_iff.mpr hKN,
      hKc.image hf.continuous⟩

/-- A finite-type complex scheme has a second-countable ordinary point space.
Quasi-compactness supplies a finite subcover of the genuine affine cover. -/
theorem schemePoints_secondCountable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    SecondCountableTopology (SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : CompactSpace Foundations.Scheme.ProjectiveSpace.complexBase := inferInstanceAs (CompactSpace (PrimeSpectrum ℂ))
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let 𝒰 := X.left.affineCover.finiteSubcover
  let : ∀ i : 𝒰.I₀, SecondCountableTopology
      (SchemePointHomeomorphs.schemeComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i)) := fun i => by
    let : IsAffine (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i).left :=
      inferInstanceAs (IsAffine (𝒰.X i))
    let : LocallyOfFiniteType (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝒰.f i ≫ X.hom))
    exact affineSchemePoints_secondCountable (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i)
  have hq := SchemePointHomeomorphs.schemeComplexPoints.isOpenQuotientMap_openCoverSigmaPointMap X 𝒰
  exact Topology.IsOpenQuotientMap.secondCountableTopology hq

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
