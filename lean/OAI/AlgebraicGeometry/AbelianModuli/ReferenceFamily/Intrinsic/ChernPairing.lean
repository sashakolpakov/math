import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing

/-! # Chern Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing

noncomputable section

/-! The actual Chern class of an algebraic line bundle yields a rational
alternating pairing on the native period span, through genuine singular
homology products and algebraic group multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter

def nativeMultiplication (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace A.toOver) ⟶ Betti.Scheme.schemePointSpace A.toOver := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  let m : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := ⟨fun p => p.1 * p.2,
    (HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.contMDiff_product_map (MonObj.mul (X := A.toOver))).continuous⟩
  exact TopCat.ofHom m

def nativeChernForm (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) :
    RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] ℚ :=
  (HomologyCrossPairing.alternatingClassPairing (Betti.Scheme.schemePointSpace A.toOver) (nativeMultiplication A)
    (ChernClasses.lineBundleChernClass A.variety.presentation L)).compl₁₂
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap

theorem nativeChernForm_alternating (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : nativeChernForm A L v v = 0 :=
  HomologyCrossPairing.alternatingClassPairing_alternating _ _ _ _

theorem nativeChernForm_iso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L M : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (e : L.sheaf ≅ M.sheaf) : nativeChernForm A L = nativeChernForm A M := by
  unfold nativeChernForm
  rw [ChernClasses.lineBundleChernClass_iso A.variety.presentation L M e]

variable {g N : ℕ} {δ : Fin g → ℕ}
  (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

def polarizationFiberLineBundle : HilbertConstruction.Line.Bundles.LineBundle (A.abelian.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).scheme.left :=
  Classical.choose (A.polarization.positive ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))

theorem polarizationFiberLineBundle_ample : (polarizationFiberLineBundle A).IsAmple :=
  (Classical.choose_spec (A.polarization.positive ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))).1

theorem polarizationFiberLineBundle_poincare :
    let B := (A.abelian.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).scheme
    let L := polarizationFiberLineBundle A
    Nonempty (HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (HilbertConstruction.Tensor.ProductSheaf.tensorModule
        (HilbertConstruction.PolarizationData.polarizationBiextensionAt A.dual A.polarization.isogeny.hom (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).sheaf
        (HilbertConstruction.Line.Bundles.LineBundle.pullback (CategoryTheory.CartesianMonoidalCategory.fst B B).left L).sheaf)
      (HilbertConstruction.Line.Bundles.LineBundle.pullback (CategoryTheory.CartesianMonoidalCategory.snd B B).left L).sheaf ≅
        (HilbertConstruction.Line.Bundles.LineBundle.pullback (MonObj.mul (X := B)).left L).sheaf) :=
  (Classical.choose_spec (A.polarization.positive ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))).2.2

/-- The bundle is chosen from the actual polarization witness and then
transported from the identity pullback to the original scheme. -/
def polarizationLineBundle : HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left :=
  (polarizationFiberLineBundle A).pullback A.abelian.pullbackIdIso.inv.left

theorem polarizationLineBundle_ample : (polarizationLineBundle A).IsAmple := by
  let f := A.abelian.pullbackIdIso.inv.left
  let : IsIso f := inferInstanceAs
    (IsIso (((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso A.abelian.pullbackIdIso).inv))
  exact (polarizationFiberLineBundle_ample A).pullback_of_isIso f

/-- A rational alternating form constructed from the polarization's
actual ample bundle, its native first Chern class and native periods.
Its nondegeneracy and Rosati compatibility are subsequent obligations. -/
def nativePolarizationForm :
    RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) →ₗ[ℚ]
      RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) →ₗ[ℚ] ℚ :=
  nativeChernForm (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) (polarizationLineBundle A)

theorem nativePolarizationForm_alternating
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    nativePolarizationForm A v v = 0 := nativeChernForm_alternating _ _ v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing
