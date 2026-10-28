import OAI.RepresentationTheory.Theta.Geometric.DifferencePicardClasses
import OAI.RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality

/-! # Infinitesimal Difference Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.InfinitesimalDifferenceIso

noncomputable section

/-! On a one-point test scheme, a trivial difference fiber gives an
actual isomorphism from the translated line bundle to the original one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterDifference_trivial_translation_iso {d : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Nonempty T.left] [Subsingleton T.left] (t : T ⟶ A.scheme)
    (ht : ParameterizedPicardClass.parameterLineClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) t = 1) :
    Nonempty (((L.pullback (snd T A.scheme).left).pullback (A.translation t).left).sheaf ≅
      (L.pullback (snd T A.scheme).left).sheaf) := by
  have hbase : Picard.PicardPullback.picardPullback t.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 :=
    Quotient.sound (LineBundleFieldTriviality.lineBundle_trivial_of_subsingleton (L.pullback t.left))
  have H := (DifferencePicardClasses.parameterDifference_class A L t).symm.trans ht
  rw [hbase, map_one, inv_one, mul_one] at H
  have H' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((L.pullback (snd T A.scheme).left).pullback (A.translation t).left) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd T A.scheme).left) := mul_inv_eq_one.mp H
  exact Quotient.exact H'

end

end OAI.RepresentationTheory.Theta.Geometric.InfinitesimalDifferenceIso
