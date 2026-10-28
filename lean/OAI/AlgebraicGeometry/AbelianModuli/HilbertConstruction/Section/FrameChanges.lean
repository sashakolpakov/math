import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmbeddingFrameCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport

/-! # Frame Changes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameChanges

noncomputable section

/-! Two complete section families of isomorphic line bundles differ by
an actual invertible coefficient transformation. The transformation
commutes with the section maps and has an explicit inverse. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v w
variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
variable (c : R →+* Γ(X, ⊤)) {M Q : X.Modules}
variable (s : ι → (Line.Bundles.structureModule X ⟶ M)) (t : κ → (Line.Bundles.structureModule X ⟶ Q))
variable (hs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s))
variable (ht : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c Q t))
variable (e : M ≅ Q)

def completeSectionFrameChange : (ι →₀ R) ≃ₗ[R] (κ →₀ R) :=
  (LinearEquiv.ofBijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s) hs).trans
    ((Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv c e).trans
      (LinearEquiv.ofBijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c Q t) ht).symm)

theorem completeSectionFrameChange_commutes (a : ι →₀ R) :
    Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c Q t (completeSectionFrameChange c s t hs ht e a) =
      Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv c e (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s a) :=
  (LinearEquiv.ofBijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c Q t) ht).apply_symm_apply _

theorem completeSectionFrameChange_inverse (a : ι →₀ R) :
    (completeSectionFrameChange c s t hs ht e).symm
      (completeSectionFrameChange c s t hs ht e a) = a :=
  (completeSectionFrameChange c s t hs ht e).symm_apply_apply a

theorem completeSectionFrameChange_single (i : ι) :
    Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c Q t
      (completeSectionFrameChange c s t hs ht e (Finsupp.single i 1)) =
    Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c Q (s i ≫ e.hom) := by
  exact (completeSectionFrameChange_commutes c s t hs ht e _).trans
    ((congrArg (Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv c e)
      (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_single c M s i)).trans
        (Coefficient.SectionBundleTransport.coefficientRingSectionAddEquiv_postcomp c e.hom (s i)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameChanges
