import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter

/-! # Period Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter

noncomputable section

/-! Rational period maps of morphisms between the original HilbertConstruction schemes,
with the actual native presentations supplied explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

variable {g h : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)

theorem nativeComparisonMap_eq (f : A.scheme ⟶ B.scheme) :
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv = f := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ f.left ≫ 𝟙 _ = f.left
  simp only [Category.id_comp, Category.comp_id]

theorem nativeOriginalMap_isMonHom (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    IsMonHom (show (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA).toOver ⟶ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB).toOver from f) := by
  have hf : IsMonHom ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv) := inferInstance
  exact (nativeComparisonMap_eq A B PA PB f) ▸ hf

def originalPeriodMap (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) := by
  let := nativeOriginalMap_isMonHom A B PA PB f
  exact Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (A := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) (B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) f

def originalPeriodIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) := by
  let := nativeOriginalMap_isMonHom A B PA PB e.hom
  exact Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso (A := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) (B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) e

theorem originalPeriodMap_faithful (f t : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom t]
    (ht : originalPeriodMap A B PA PB f = originalPeriodMap A B PA PB t) : f = t := by
  let := nativeOriginalMap_isMonHom A B PA PB f
  let := nativeOriginalMap_isMonHom A B PA PB t
  exact Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful (A := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) (B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) f t ht

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter
