import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InvariantAffine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

/-! # Section Affine -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionAffine.Construction

noncomputable section

/-! Affineness of a descended section's nonvanishing locus is detected
on the actual finite-flat quotient with its finite-free kernel relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

universe u v

theorem quotient_sectionNonvanishing_isAffineOpen
    {H S R X Y : Scheme.{u}} [IsAffine H] [IsAffine S]
    (q : X ⟶ Y) [Flat q] [Surjective q] [QuasiCompact q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t)
    (h : H ⟶ S) [IsFinite h] (a : X ⟶ S) (r : R ⟶ H)
    (hs : IsPullback r s h a) {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf)
    (hz : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q z))) :
    IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) := by
  let W := q ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z
  have hW : IsAffineOpen W :=
    (congrArg IsAffineOpen (AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange q L z)).mp hz
  have hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W := by
    dsimp only [W]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hk.w]
  have hdesc := InvariantAffine.Construction.invariantAffineOpen_descends q s t hk h a r hs b W hW hinv
  exact (Quotients.FiniteDescent.InvariantOpensEq.Construction.InvariantOpens.descend_unique q hk W hinv
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) rfl).symm ▸ hdesc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionAffine.Construction
