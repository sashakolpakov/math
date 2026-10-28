import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.TranslationIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.MultiplicationIsomorphism

/-! # Pair Bilinearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Poincare evaluation is multiplicative in both arguments over arbitrary test schemes over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) {T : Over (Spec (.of K))}

theorem Dual.Data.DualAbelianData.poincarePair_mul_left (f h : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    Nonempty ((D.poincarePair (f * h) a).sheaf ≅
      ((D.poincarePair f a).tensor (D.poincarePair h a)).sheaf) := by
  obtain ⟨e⟩ := D.poincareAt_mul_iso_overField f h
  exact ⟨(Scheme.Modules.pullback (A.familyPointSection T a)).mapIso e ≪≫
    Line.Bundles.LineBundle.tensorBaseChangeIso (A.familyPointSection T a) (D.poincareAt f) (D.poincareAt h)⟩

theorem Dual.Data.DualAbelianData.poincarePair_mul_right (f : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme) :
    Nonempty ((D.poincarePair f (a * b)).sheaf ≅
      ((D.poincarePair f a).tensor (D.poincarePair f b)).sheaf) := by
  obtain ⟨e⟩ := Dual.Data.DualAbelianData.poincareAt_translation_iso A D f a
  exact ⟨(PointSectionTranslation.translatedBundle_pointIso A T a b (D.poincareAt f)).symm ≪≫
    (Scheme.Modules.pullback (A.familyPointSection T b)).mapIso e ≪≫
    Line.Bundles.LineBundle.tensorBaseChangeIso (A.familyPointSection T b) (D.poincareAt f)
      ((D.poincarePair f a).pullback (Limits.pullback.fst T.hom A.scheme.hom)) ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (PointSectionTranslation.baseBundle_pointIso A T b (D.poincarePair f a)) ≪≫
    Tensor.ProductSheaf.tensorModuleCommIso (D.poincarePair f b).sheaf (D.poincarePair f a).sheaf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
