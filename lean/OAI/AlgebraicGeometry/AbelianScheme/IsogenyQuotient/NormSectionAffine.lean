import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalNormSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionInvariantAffine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionAffine

/-! # Norm Section Affine -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionAffine.Construction

noncomputable section

/-! Norm sections with affine source nonvanishing locus have affine
target nonvanishing locus in the actual finite-flat quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem finiteFlatNormSection_preimage_core {R X Y : Scheme.{u}}
    (q : X ⟶ Y) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t) [IsFinite s]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ) (hdegree : ∀ y : Y, q.finrank y = d)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    q ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree z) =
      Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core s t (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) := by
  ext x
  change q x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree z) ↔
    x ∈ Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core s t (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z)
  rw [GlobalNormSection.Construction.finiteFlatNormSection_mem_nonvanishing, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.mem_core]
  simp_rw [SectionInvariantAffine.Construction.kernelPair_related_iff q s t hk x]
  exact ⟨fun h y hy => h y hy.symm, fun h y hy => h y hy.symm⟩

theorem finiteFlatNormSection_isAffineOpen
    {H S R X Y : Scheme.{u}} [IsAffine H] [IsAffine S]
    (q : X ⟶ Y) [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t)
    (h : H ⟶ S) [IsFinite h] (a : X ⟶ S) (r : R ⟶ H)
    (hs : IsPullback r s h a) {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ) (hdegree : ∀ y : Y, q.finrank y = d)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf)
    (hz : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z)) :
    IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree z)) := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  have : IsAffine (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z).toScheme := hz
  obtain ⟨bD⟩ := Quotients.FiniteDescent.InvariantAffineHas.Construction.InvariantAffineBasis.exists_basis_restrict h a r s hs b (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z)
  have hcore := SectionInvariantAffine.Construction.sectionInvariantCore_isAffineOpen q s t hk L z hz bD
  apply SectionAffine.Construction.quotient_sectionNonvanishing_isAffineOpen q s t hk h a r hs b (L.tensorPower d)
    (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree z)
  rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange q (L.tensorPower d),
    finiteFlatNormSection_preimage_core q s t hk L d hdegree z]
  exact hcore

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionAffine.Construction
