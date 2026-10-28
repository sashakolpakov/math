import OAI.RepresentationTheory.Theta.Geometric.InfinitesimalDifferenceIso
import OAI.RepresentationTheory.Theta.Geometric.Normalized.ParameterClassEquality

/-! # Descended Infinitesimal Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison

noncomputable section

/-! A trivial Picard parameter in the descended family produces an
actual translation comparison on a one-point test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem descendedParameter_trivial_translation_iso {d e : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme e AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : A.scheme ⟶ B.scheme) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ A.scheme).left)
    (recover : (Q.pullback (p ⊗ₘ 𝟙 A.scheme).left).sheaf ≅ (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf)
    (eA : (Q.pullback (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left)
    (eB : (Q.pullback (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Nonempty T.left] [Subsingleton T.left]
    [CompactSpace T.left] [QuasiSeparatedSpace T.left] (t : T ⟶ A.scheme)
    (ht : ParameterizedPicardClass.parameterPicardClass Q (t ≫ p) = ParameterizedPicardClass.parameterPicardClass Q (1 : T ⟶ B.scheme)) :
    Nonempty (((L.pullback (snd T A.scheme).left).pullback (A.translation t).left).sheaf ≅
      (L.pullback (snd T A.scheme).left).sheaf) := by
  apply InfinitesimalDifferenceIso.parameterDifference_trivial_translation_iso A L t
  have hr : ParameterizedPicardClass.parameterLineClass Q (t ≫ p) = ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) t :=
    (ParameterizedPicardClass.parameterLineClass_baseChange Q p t).trans (DifferencePicardClasses.parameterLineClass_congr _ _ recover t)
  have hline := (Normalized.ParameterClassEquality.parameterPicard_eq_iff_lineClass_eq A Q eA (t ≫ p) (1 : T ⟶ B.scheme)).mp ht
  exact hr.symm.trans (hline.trans (ParameterizedPicardClass.parameterLineClass_one Q eB T))

end

end OAI.RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison
