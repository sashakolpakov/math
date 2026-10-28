import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundlePicardPullbackComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison

/-! # Bundle Intrinsic Dual Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleIntrinsicDualMap.Construction.IntrinsicPicardPullback

noncomputable section

/-! PoincareBundle's represented dual pullback is the literal native dual map used
by the full FrobeniusKernel quotient witness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

theorem e45RepresentedDualMap_eq :
    Picard.PoincareBundle.DualMaps.representedDualMap
        (Picard.PoincareBundle.SharedRepresentation.representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
        (Picard.PoincareBundle.SharedRepresentation.representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f =
      PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB :=
  (BundlePicardPullbackComparison.Construction.e45RepresentedDualMap_eq_unbundled f
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)).trans (UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled f DA DB).symm

theorem e45Pullback_eq (ell : B.scheme ⟶ DB.abelian.scheme) :
    f ≫ ell ≫ Picard.PoincareBundle.DualMaps.representedDualMap
        (Picard.PoincareBundle.SharedRepresentation.representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
        (Picard.PoincareBundle.SharedRepresentation.representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f =
      f ≫ ell ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB :=
  congrArg (fun d => f ≫ ell ≫ d) (e45RepresentedDualMap_eq f DA DB)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleIntrinsicDualMap.Construction.IntrinsicPicardPullback
