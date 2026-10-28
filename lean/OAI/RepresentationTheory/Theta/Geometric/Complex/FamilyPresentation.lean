import OAI.RepresentationTheory.Theta.Geometric.Complex.PELClassification
import OAI.ArithmeticGeometry.Descent.CMVariety.PulledBackPresentations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity

/-! # Family Presentation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.FamilyPresentation

noncomputable section

/-! Every actual complex fiber of the pulled-back universal PEL family
has its native projective abelian presentation, with no new model input. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity

def pelNativePresentation {R : Type} [CommRing R] {g N : ℕ}
    (F : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {δ : Fin g → ℕ} {c : R →+* R}
    (hF : F.IsPEL δ c) : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation F.abelian where
  variety := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (F.toPolarized hF))
  comparison := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso F.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (F.toPolarized hF))).symm
  comparison_group := inferInstanceAs
    (IsMonHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso F.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (F.toPolarized hF))).inv)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ D.complexSpace)

def complexUniversalFiberPresentation (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation ((PELClassification.complexUniversalFamily D f).abelian.pullback x.left) :=
  ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.pullbackComp D.model.family.abelian (PELClassification.complexModelMap D f).left x.left
    (pelNativePresentation (D.model.family.pullback (x.left ≫ (PELClassification.complexModelMap D f).left))
      (PELClassification.complexUniversalFiber_isPEL D hg f x))

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.FamilyPresentation
