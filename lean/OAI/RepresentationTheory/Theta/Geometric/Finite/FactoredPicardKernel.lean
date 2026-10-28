import OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterPicardEquality
import OAI.RepresentationTheory.Theta.Geometric.Finite.TypePicardKernel

/-! # Factored Picard Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.FactoredPicardKernel

noncomputable section

/-! Finite-type Picard separation extends to arbitrary parameter
algebras for maps which factor through a finite-type affine scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    [LocallyOfFiniteType P.hom] [IsSeparated P.hom]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    (hpoints : Function.Injective (fun t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q t))

include eQ hinj hpoints in
theorem parameterPicardClass_finiteType_factored_kernel
    {B R : Type} [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
    [Algebra B R] [IsScalarTower ℂ B R] [Algebra.FiniteType ℂ B]
    (r : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ P)
    (hQ : ParameterizedPicardClass.parameterPicardClass Q (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ≫ r) =
      ParameterizedPicardClass.parameterPicardClass Q (1 : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P)) :
    Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ≫ r = 1 := by
  obtain ⟨S, hS, hs⟩ := ParameterPicardEquality.exists_fg_parameterPicard_eq A Q eQ r (1 : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ P)
    (by simpa only [MonObj.comp_one] using hQ)
  have : Algebra.FiniteType B S := S.fg_iff_finiteType.mp hS
  have : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (R := ℂ) (S := B) (A := S) inferInstance inferInstance
  have hr : Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ≫ r = 1 := TypePicardKernel.parameterPicardClass_finiteType_kernel A Q eQ hinj hpoints
    (Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ≫ r) (by simpa only [MonObj.comp_one] using hs)
  rw [← Complex.AlgebraParameterMap.complexAlgebraParameterMap_subalgebra_factor B R S, Category.assoc, hr, MonObj.comp_one]

include eQ hinj hpoints in
theorem parameterPicardClass_affine_factored_kernel
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [LocallyOfFiniteType X.hom] (j : X ⟶ P)
    {R : Type} [CommRing R] [Algebra ℂ R] (r : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X)
    (hQ : ParameterizedPicardClass.parameterPicardClass Q (r ≫ j) = ParameterizedPicardClass.parameterPicardClass Q (1 : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P)) : r ≫ j = 1 := by
  obtain ⟨B, hB, rB, hrB⟩ := TypePicardKernel.exists_fg_affineTest_factorization X r
  have : Algebra.FiniteType ℂ B := B.fg_iff_finiteType.mp hB
  have hp : Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ≫ (rB ≫ j) = r ≫ j := by
    change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B R B.val ≫ (rB ≫ j) = _
    rw [← Category.assoc, hrB]
  have h := parameterPicardClass_finiteType_factored_kernel A Q eQ hinj hpoints (rB ≫ j)
    (R := R) (hp ▸ hQ)
  exact hp.symm.trans h

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.FactoredPicardKernel
