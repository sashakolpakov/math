import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.BaseChangeFunctionSheaf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover

/-! # Picard Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PicardFunctions.RelativePicardFunctions

noncomputable section

/-! Functions on every product test of an abelian family over a locally
noetherian base, with no reducedness or flatness condition on the test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem isIso_product_app {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (T : Over S) (U : T.left.Opens) :
    IsIso ((fst T A.scheme).left.app U) :=
  Abelian.BaseChangeFunctionSheaf.abelian_baseChange_function_app_isIso A (snd T A.scheme).left
    (fst T A.scheme).left T.hom
    (IsPullback.of_hasPullback T.hom A.scheme.hom).flip U

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PicardFunctions.RelativePicardFunctions
