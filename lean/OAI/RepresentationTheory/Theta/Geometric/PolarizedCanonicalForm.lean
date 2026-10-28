import OAI.RepresentationTheory.Theta.Geometric.PresentedDiagonalForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm
import OAI.RepresentationTheory.Theta.Geometric.Complex.FamilyPresentation

/-! # Polarized Canonical Form -/

namespace OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm

noncomputable section

section

/-! Canonical presentations and genuine geometric polarization
witnesses of the actual original abelian-scheme fibers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm

variable {g N : ℕ} {δ : Fin g → ℕ}

def polarizedNativePresentation (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation A.abelian where
  variety := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  comparison := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)).symm
  comparison_group := inferInstanceAs
    (IsMonHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)).inv)

variable {S : Scheme.{0}} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (s : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)

def geometricPolarizationLine : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.abelian.pullback s).scheme.left :=
  Classical.choose (A.polarization.positive ℂ s)

theorem geometricPolarizationLine_ample : (geometricPolarizationLine A s).IsAmple :=
  (Classical.choose_spec (A.polarization.positive ℂ s)).1

theorem geometricPolarizationLine_formula :
    let B := (A.abelian.pullback s).scheme
    Nonempty (((AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt A.dual A.polarization.isogeny.hom s).tensor
      ((geometricPolarizationLine A s).pullback (CategoryTheory.CartesianMonoidalCategory.fst B B).left) |>.tensor
        ((geometricPolarizationLine A s).pullback (CategoryTheory.CartesianMonoidalCategory.snd B B).left)).sheaf ≅
          ((geometricPolarizationLine A s).pullback (MonObj.mul (X := B)).left).sheaf) :=
  (Classical.choose_spec (A.polarization.positive ℂ s)).2.2

theorem geometricPolarizationLine_form :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm (polarizedNativePresentation (A.pullback s)).variety (geometricPolarizationLine A s) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm (A.pullback s) := by
  obtain ⟨e⟩ := geometricPolarizationLine_formula A s
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm.nativePolarizationForm_of_witness (A.pullback s) (geometricPolarizationLine A s)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt A.dual A.polarization.isogeny.hom s)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Biextension.polarizationBiextensionAt_class A s) e

end

section

/-! The total diagonal line has twice the original canonical native
polarization form on each actual fiber, independently of the ample witness. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm

variable {g N : ℕ} {δ : Fin g → ℕ} {S : Scheme.{0}}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (s : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)

theorem canonicalDiagonalForm
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (polarizedNativePresentation (A.pullback s)).variety) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm (polarizedNativePresentation (A.pullback s)).variety
      (PresentedDiagonalLine.presentedRelativeDiagonalLine A.dual A.polarization.isogeny.hom s
        (polarizedNativePresentation (A.pullback s))) v w =
      2 * AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm (A.pullback s) v w := by
  let P := polarizedNativePresentation (A.pullback s)
  let L := geometricPolarizationLine A s
  obtain ⟨e⟩ := geometricPolarizationLine_formula A s
  have h := PresentedDiagonalForm.presentedRelativeDiagonalForm A.dual A.polarization.isogeny.hom s P L e v w
  have hi : (L.pullback P.comparison.inv.left).sheaf ≅ L.sheaf :=
    (Scheme.Modules.pullbackId (A.abelian.pullback s).scheme.left).app L.sheaf
  have hc := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm_iso P.variety (L.pullback P.comparison.inv.left) L hi
  have hw := geometricPolarizationLine_form A s
  exact h.trans (congrArg (fun b => 2 * b v w) (hc.trans hw))

end

/-! The original canonical polarization form on each literal complex fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)

def polarizedFamilyPresentation (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (A.abelian.pullback y.left) :=
  polarizedNativePresentation (A.pullback y.left)

def familyPolarizationForm (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (polarizedFamilyPresentation A y).variety →ₗ[ℚ]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (polarizedFamilyPresentation A y).variety →ₗ[ℚ] ℚ :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm (A.pullback y.left)

theorem familyPolarizationForm_original (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    familyPolarizationForm A y = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm (A.pullback y.left) := rfl

theorem familyDiagonalForm (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (polarizedFamilyPresentation A y).variety) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm (polarizedFamilyPresentation A y).variety
      (PresentedDiagonalLine.presentedRelativeDiagonalLine A.dual A.polarization.isogeny.hom y.left
        (polarizedFamilyPresentation A y)) v w = 2 * familyPolarizationForm A y v w :=
  canonicalDiagonalForm A y.left v w

end

end OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm
