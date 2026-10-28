import OAI.AlgebraicGeometry.ComplexMultiplication.CMComparisonTo
import OAI.AlgebraicGeometry.Cohomology.SingularComparison
import OAI.Algebra.Homology.Notation

/-! # Scalars -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Scalars

noncomputable section

/-! # Scalar maps on the actual singular-cochain resolution -/

open _root_.CategoryTheory Limits OAI.AlgebraicTopology.Singular _root_.AlgebraicGeometry ComplexPoint

variable (R : Type) [CommRing R] (Y : TopCat.{0}) (q : R)

/-- Multiply the values of every original singular cochain by the given coefficient. -/
def singularCochainPresheafScalar (n : ℕ) :
    AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R Y n ⟶ AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R Y n where
  app U := AddCommGrpCat.ofHom
    (DistribSMul.toAddMonoidHom (AlgebraicTopology.Singular.SheafCochain.OpenCochains R Y U n) q)
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext φ
    change AlgebraicTopology.Singular.SheafCochain.OpenCochains R Y U n at φ
    apply LinearMap.ext
    intro c
    rfl

/-- Scalar multiplication commutes with the original singular coboundary. -/
def singularCochainPresheafComplexScalar :
    AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex R Y ⟶ AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex R Y where
  f n := singularCochainPresheafScalar R Y q n
  comm' i j hij := by
    obtain rfl := hij
    rw [AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex_d]
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    ext φ
    change AlgebraicTopology.Singular.SheafCochain.OpenCochains R Y U i at φ
    apply LinearMap.ext
    intro c
    rfl

/-- Sheafification of the same scalar chain map. -/
def singularCochainSheafComplexScalar :
    AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R Y ⟶ AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R Y :=
  ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (singularCochainPresheafComplexScalar R Y q)

/-- The scalar map on the original integer-indexed singular-cochain sheaf complex. -/
def singularCochainSheafComplexIntScalar (X : Over (Spec ↧ℂ)) :
    ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R ⟶ ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R :=
  HomologicalComplex.extendMap
    (singularCochainSheafComplexScalar R ↧(ComplexPoint.Basic.ComplexSchemePoint X) q) ComplexShape.embeddingUpNat

/-- The constant zero-cochain construction is coefficient-linear. -/
lemma constantsToSingularCochainZero_scalar :
    ((Functor.const (TopologicalSpace.Opens Y)ᵒᵖ).map
      (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom R q))) ≫
        AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R Y =
      AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R Y ≫ singularCochainPresheafScalar R Y q 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext r
  change R at r
  apply LinearMap.ext
  intro c
  change (q * r) * (AlgebraicTopology.Singular.SheafCochain.openZeroAugmentation R Y U).hom c =
    q * (r * (AlgebraicTopology.Singular.SheafCochain.openZeroAugmentation R Y U).hom c)
  exact mul_assoc _ _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Scalars
