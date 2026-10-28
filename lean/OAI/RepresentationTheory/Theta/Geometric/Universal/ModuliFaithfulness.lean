import OAI.RepresentationTheory.Theta.Geometric.Complex.PELClassification
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # Moduli Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.ModuliFaithfulness

noncomputable section

/-! The original reduced-test fine-moduli classification distinguishes
complex points whenever their complete PEL fibers are isomorphic. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem complexPELPoint_eq_of_iso (hg : D.HasIntegralModelGeometry)
    (x y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.complexSpace)
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D x).left)
      (D.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D y).left)) : x = y := by
  let : IsReduced (Over.mk D.complexPoint).left := inferInstanceAs (IsReduced (Spec (.of ℂ)))
  obtain ⟨t, _, hu⟩ := hg.classifies.2 (Over.mk D.complexPoint)
    (D.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D y).left)
    (hg.classifies.1 (Over.mk D.complexPoint) (Complex.PELClassification.modelComplexPointEquiv D y))
  apply (Complex.PELClassification.modelComplexPointEquiv D).injective
  exact (hu (Complex.PELClassification.modelComplexPointEquiv D x) ⟨e⟩).trans
    (hu (Complex.PELClassification.modelComplexPointEquiv D y) ⟨AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _⟩).symm

def complexUniversalFiber_modelIso {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D (x ≫ f)).left)
      ((Complex.PELClassification.complexUniversalFamily D f).pullback x.left) :=
  D.model.family.pullbackFactor x.left (Complex.PELClassification.complexModelMap D f).left
    (Complex.PELClassification.modelComplexPointEquiv D (x ≫ f)).left (Complex.PELClassification.complexModelMap_point D f x).symm

theorem complexUniversal_point_eq_of_iso (hg : D.HasIntegralModelGeometry) {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : S ⟶ D.complexSpace) (x y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((Complex.PELClassification.complexUniversalFamily D f).pullback x.left)
      ((Complex.PELClassification.complexUniversalFamily D f).pullback y.left)) : x ≫ f = y ≫ f :=
  complexPELPoint_eq_of_iso D hg (x ≫ f) (y ≫ f)
    ((complexUniversalFiber_modelIso D f x).trans
      (e.trans (complexUniversalFiber_modelIso D f y).symm))

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.ModuliFaithfulness
