import OAI.RepresentationTheory.Theta.Geometric.Universal.PELConditions
import OAI.RepresentationTheory.Theta.Geometric.Complex.BaseFiberCharacter

/-! # Distinguished Rank -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.DistinguishedRank

noncomputable section

section

/-! The original universal family's prescribed signature gives the
actual distinguished Lie rank two at every complex test point. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.complexSpace)

theorem complexUniversal_distinguished_rank (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank ((PELConditions.complexUniversalPolarized D hg f).abelian.pullback x.left)
      ((PELConditions.complexUniversalAction D hg f).pullback x.left)
      (D.reference.μ.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2 := by
  have h := (PELConditions.complexUniversal_isPELFamily D hg f).2 ℂ x.left (AlgEquiv.refl : E ≃ₐ[ℚ] E)
  rw [Reference.LieSignature.actionFromEnd_baseChange, Complex.BaseFiberCharacter.referenceComplexBaseAction_fiber,
    Complex.BaseFiberCharacter.reference_lieRank_identity D.reference hg.reference_admissible] at h
  have hc : (D.reference.μ.comp (algebraMap (NumberField.RingOfIntegers E) E)).comp
      (NumberField.RingOfIntegers.mapAlgEquiv (AlgEquiv.refl : E ≃ₐ[ℚ] E)).toRingHom =
      D.reference.μ.comp (algebraMap (NumberField.RingOfIntegers E) E) := by
    apply RingHom.ext
    intro a
    rfl
  rw [hc] at h
  exact h

end

/-! The original universal-family signature retains every selected
embedding rank, including all compact blocks, at every actual point. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.complexSpace)

theorem complexUniversal_embedding_rank (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (i : Fin s) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank ((PELConditions.complexUniversalPolarized D hg f).abelian.pullback x.left)
      ((PELConditions.complexUniversalAction D hg f).pullback x.left)
      ((D.reference.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E))
      (D.reference.firstLieRank i) := by
  obtain ⟨τ, hτ⟩ := AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingLieIndices.embedding_eq_comp_aut (D.reference.embeddings D.reference.distinguished) (D.reference.embeddings i)
  have h := (PELConditions.complexUniversal_isPELFamily D hg f).2 ℂ x.left τ
  rw [Reference.LieSignature.actionFromEnd_baseChange, Complex.BaseFiberCharacter.referenceComplexBaseAction_fiber] at h
  have hc : (D.reference.μ.comp (algebraMap (NumberField.RingOfIntegers E) E)).comp
      (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom =
      (D.reference.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E) := by
    have ht : (D.reference.μ.comp (algebraMap (NumberField.RingOfIntegers E) E)).comp
        (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom =
        (D.reference.μ.comp τ.toRingHom).comp (algebraMap (NumberField.RingOfIntegers E) E) := by
      apply RingHom.ext
      intro a
      rfl
    exact ht.trans (congrArg (fun t : E →+* ℂ => t.comp (algebraMap (NumberField.RingOfIntegers E) E)) hτ)
  rw [hc, D.reference.lieRank_of_embedding hg.reference_admissible τ i hτ] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.DistinguishedRank
