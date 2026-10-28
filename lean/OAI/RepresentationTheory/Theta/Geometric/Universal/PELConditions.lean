import OAI.RepresentationTheory.Theta.Geometric.Complex.PELClassification

/-! # PEL Conditions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.PELConditions

noncomputable section

/-! The original reduced-test moduli classification supplies the full
PEL and signature conditions on the actual pulled-back universal family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.complexSpace)

include hg in
theorem complexUniversal_isPELFamily :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.IsPELFamily D.reference (S.hom.appTop.hom.comp (Reference.LieSignature.referenceComplexBaseAction D.reference))
      (Complex.PELClassification.complexUniversalFamily D f) := by
  let : IsReduced (Over.mk (S.hom ≫ D.complexPoint)).left := inferInstanceAs (IsReduced S.left)
  have h := hg.classifies.1 (Over.mk (S.hom ≫ D.complexPoint)) (Complex.PELClassification.complexModelMap D f)
  have he : (S.hom ≫ D.complexPoint).appTop.hom.comp D.baseAction =
      S.hom.appTop.hom.comp (Reference.LieSignature.referenceComplexBaseAction D.reference) := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc, Complex.PELBaseAction.complexPELBaseAction D hg]
  change AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.IsPELFamily D.reference ((S.hom ≫ D.complexPoint).appTop.hom.comp D.baseAction)
    (Complex.PELClassification.complexUniversalFamily D f) at h
  rw [he] at h
  exact h

def complexUniversalPolarized :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) D.reference.polarizationType D.level S.left :=
  (Complex.PELClassification.complexUniversalFamily D f).toPolarized (complexUniversal_isPELFamily D hg f).1

def complexUniversalAction :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (complexUniversalPolarized D hg f).abelian :=
  AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd (Complex.PELClassification.complexUniversalFamily D f).action

theorem complexUniversal_rosati :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (complexUniversalPolarized D hg f) (complexUniversalAction D hg f) := by
  intro a
  obtain ⟨d, hd, hp⟩ := (complexUniversal_isPELFamily D hg f).1.2.2 a
  exact ⟨AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap (Complex.PELClassification.complexUniversalFamily D f).dual.abelian.scheme d,
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_isMonHom (Complex.PELClassification.complexUniversalFamily D f).dual.abelian.scheme d, hd.symm, hp⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.PELConditions
