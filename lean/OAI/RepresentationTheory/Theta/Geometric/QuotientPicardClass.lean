import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation

/-! # Quotient Picard Class -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientPicardClass

noncomputable section

/-! The native theta quotient has the expected quotient in the intrinsic
Picard group, including the actual negative hyperplane twist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

local instance thetaQuotientPicardMonoidal (X : Scheme) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def algebraicTwistOneCancellationIso (n : ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AlgebraicQuotient.algebraicTwistBundle n (-1)).sheaf (AlgebraicQuotient.algebraicTwistBundle n 1).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :=
  (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso (AlgebraicQuotient.algebraicTwistBundle n (-1)).sheaf (AlgebraicQuotient.algebraicTwistBundle n 1).sheaf).symm ≪≫
    ((λ_ (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModule (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := ℂ) (0 : Fin (n + 1))))) ⊗ᵢ
      (λ_ (AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := ℂ) (0 : Fin (n + 1))))) ≪≫
    AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso _ _ ≪≫
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation.Scheme.Modules.invertibleEvaluationIso
      (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneIdeal.MvPolynomial.coordinateHyperplaneIdealModule_isInvertible (R := ℂ) (0 : Fin (n + 1)))

theorem algebraicTwist_neg_one_class (n : ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n (-1)) =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n 1))⁻¹ := by
  have h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n (-1)) *
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n 1) = 1 :=
    Quotient.sound ⟨algebraicTwistOneCancellationIso n⟩
  exact eq_inv_iff_mul_eq_one.mpr h

theorem algebraicThetaQuotient_class {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicThetaQuotient f g) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)) *
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)))⁻¹ := by
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)) *
    Picard.PicardPullback.picardPullback f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle n (-1))) = _
  rw [algebraicTwist_neg_one_class, map_inv]
  rfl

theorem thetaQuotient_preserved_of_hyperplanes {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (t : X ⟶ X)
    (hf : Nonempty (((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)).pullback t).sheaf ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)).sheaf))
    (hg : Nonempty (((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)).pullback t).sheaf ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)).sheaf)) :
    Nonempty (((AlgebraicQuotient.algebraicThetaQuotient f g).pullback t).sheaf ≅ (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf) := by
  have hF : Picard.PicardPullback.picardPullback t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1))) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)) := Quotient.sound hf
  have hG : Picard.PicardPullback.picardPullback t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1))) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)) := Quotient.sound hg
  have h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((AlgebraicQuotient.algebraicThetaQuotient f g).pullback t) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicThetaQuotient f g) := by
    change Picard.PicardPullback.picardPullback t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicThetaQuotient f g)) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicThetaQuotient f g)
    rw [algebraicThetaQuotient_class, map_mul, map_inv, hF, hG]
  exact Quotient.exact h

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientPicardClass
