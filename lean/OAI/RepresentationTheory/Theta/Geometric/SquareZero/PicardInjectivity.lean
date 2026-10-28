import OAI.RepresentationTheory.Theta.Geometric.SquareZero.SchemeDetection
import OAI.RepresentationTheory.Theta.Geometric.Dual.PicardInjectivity
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints

/-! # Picard Injectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.PicardInjectivity

noncomputable section

/-! Picard parameter separation on actual complex dual numbers implies
separation on every split square-zero complex test, with no restriction
on the dimension of its coefficient space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
open _root_.CategoryTheory.MonoidalCategory

theorem parameterPicardClass_squareZero_injective
    {A P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (hinj : Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M] :
    Function.Injective (fun t : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ M) ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t) := by
  intro a b hab
  apply Over.OverMorphism.ext
  apply SchemeDetection.squareZero_scheme_maps_ext
  intro l
  let u : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ M) :=
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (TrivSqZeroExt ℂ M) (DualNumber ℂ) (TrivSqZeroExt.map l)
  have H : u ≫ a = u ≫ b := by
    apply hinj
    exact (ParameterizedPicardClass.parameterPicardClass_naturality Q a u).symm.trans
      ((congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map u.op) hab).trans
        (ParameterizedPicardClass.parameterPicardClass_naturality Q b u))
  have H' : u.left ≫ a.left = u.left ≫ b.left := congrArg Over.Hom.left H
  have hu : u.left = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom) :=
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv_left ℂ (TrivSqZeroExt ℂ M) (DualNumber ℂ) (TrivSqZeroExt.map l)
  exact (congrArg (fun f => f ≫ a.left) hu).symm.trans
    (H'.trans (congrArg (fun f => f ≫ b.left) hu))

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.PicardInjectivity
