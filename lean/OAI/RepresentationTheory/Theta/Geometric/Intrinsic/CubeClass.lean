import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeMaps
import OAI.RepresentationTheory.Theta.Geometric.QuotientPicardClass

/-! # Cube Class -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass

noncomputable section

/-! The cubical defect is a homomorphism of the intrinsic Picard groups.
Consequently the cubical identity is preserved by tensor products and duals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def nativeCubeDefect (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.toOver.left →*
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A).toOver.left :=
  (∏ k : Fin 4, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubePositiveMap A k).left) *
    (∏ k : Fin 3, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubeNegativeMap A k).left)⁻¹

theorem nativeCubeDefect_apply (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.toOver.left) :
    nativeCubeDefect A a =
      (∏ k : Fin 4, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubePositiveMap A k).left a) *
        (∏ k : Fin 3, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubeNegativeMap A k).left a)⁻¹ := by
  simp only [nativeCubeDefect, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.finsetProd_apply]

theorem nativeCubeDefect_eq_one_iff (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.toOver.left) :
    nativeCubeDefect A a = 1 ↔
      (∏ k : Fin 4, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubePositiveMap A k).left a) =
        ∏ k : Fin 3, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubeNegativeMap A k).left a := by
  rw [nativeCubeDefect_apply, mul_inv_eq_one]

theorem nativeCubeDefect_thetaQuotient (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {n m : ℕ}
    (f : A.toOver.left ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : A.toOver.left ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (hf : nativeCubeDefect A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1))) = 1)
    (hg : nativeCubeDefect A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1))) = 1) :
    nativeCubeDefect A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicThetaQuotient f g)) = 1 := by
  rw [QuotientPicardClass.algebraicThetaQuotient_class, map_mul, map_inv, hf, hg, inv_one, mul_one]

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass
