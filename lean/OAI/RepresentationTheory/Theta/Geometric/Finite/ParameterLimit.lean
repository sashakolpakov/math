import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst
import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps

/-! # Parameter Limit -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterLimit

noncomputable section

/-! Actual morphisms out of a constant qcqs complex family descend to a
finitely generated coefficient subalgebra. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {R : Type} [CommRing R] [Algebra ℂ R]

theorem exists_fg_constant_family_morphism
    (A X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [QuasiCompact A.hom] [QuasiSeparated A.hom]
    [LocallyOfFinitePresentation X.hom] (a : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A ⟶ X) :
    ∃ S : Subalgebra ℂ R, S.FG ∧ ∃ b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⊗ A ⟶ X,
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A) ≫ b = a := by
  obtain ⟨s, b, hb, hbase⟩ := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.scheme_morphism_descends_to_finite_coefficients
    ℂ R A.hom X.hom a.left (a.w.trans pullback.condition)
  let S := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra ℂ R s.unop
  have hbase' : b ≫ X.hom = (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⊗ A).hom :=
    hbase.trans pullback.condition.symm
  refine ⟨S, Subalgebra.fg_adjoin_finset _, Over.homMk b hbase', ?_⟩
  apply Over.OverMorphism.ext
  have hm : (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A).left =
      (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone ℂ R A.hom).π.app s := by
    apply pullback.hom_ext
    · exact (congrArg Over.Hom.left (whiskerRight_fst
        (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val) A)).trans
          (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_fst ℂ R A.hom s).symm
    · exact (congrArg Over.Hom.left (whiskerRight_snd
        (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val) A)).trans
          (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_structure ℂ R A.hom s).symm
  change (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A).left ≫ b = a.left
  rw [hm]
  exact hb

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterLimit
