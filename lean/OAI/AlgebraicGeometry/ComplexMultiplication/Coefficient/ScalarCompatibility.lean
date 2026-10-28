import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Scalars
import OAI.Algebra.Homology.Notation

/-! # Scalar Compatibility -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.ScalarCompatibility

noncomputable section

/-! # Scalar compatibility of the actual constant-to-singular comparison -/

open _root_.CategoryTheory Limits OAI.AlgebraicTopology.Singular _root_.AlgebraicGeometry ComplexPoint

variable (R : Type) [Field R] (X : Over (Spec ↧ℂ)) (q : R)

/-- The original constant-sheaf scalar map commutes with inclusion as zero-cochains. -/
lemma fieldScalarSheaf_constantsToSingularZero :
    ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf R X q ≫ AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R ↧(ComplexPoint.Basic.ComplexSchemePoint X) =
      AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R ↧(ComplexPoint.Basic.ComplexSchemePoint X) ≫
        (Scalars.singularCochainSheafComplexScalar R ↧(ComplexPoint.Basic.ComplexSchemePoint X) q).f 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  let S := presheafToSheaf J AddCommGrpCat
  change S.map ((Functor.const _).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q))) ≫
      S.map (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R ↧(ComplexPoint.Basic.ComplexSchemePoint X)) =
    S.map (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R ↧(ComplexPoint.Basic.ComplexSchemePoint X)) ≫
      S.map (Scalars.singularCochainPresheafScalar R ↧(ComplexPoint.Basic.ComplexSchemePoint X) q 0)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg S.map (Scalars.constantsToSingularCochainZero_scalar R ↧(ComplexPoint.Basic.ComplexSchemePoint X) q)

/-- The same compatibility holds for the original full nonnegative cochain resolution. -/
lemma fieldScalarSingle_constantsToSingularComplex :
    (CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map (ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf R X q) ≫
        AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X) =
      AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X) ≫
        Scalars.singularCochainSheafComplexScalar R ↧(ComplexPoint.Basic.ComplexSchemePoint X) q := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf R X q ≫
          AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R ↧(ComplexPoint.Basic.ComplexSchemePoint X) =
        AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R ↧(ComplexPoint.Basic.ComplexSchemePoint X) ≫ _
      exact fieldScalarSheaf_constantsToSingularZero R X q
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)).obj (AddCommGrpCat.of R))
        (n + 1) (Nat.succ_ne_zero n)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility for the actual integer-indexed maps used by hypercohomology. -/
lemma fieldScalarComplex_constantsToSingularInt :
    ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex R X q ≫ ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R =
      ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R ≫ Scalars.singularCochainSheafComplexIntScalar R q X := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt
    Scalars.singularCochainSheafComplexIntScalar
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    fieldScalarSingle_constantsToSingularComplex]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.ScalarCompatibility
