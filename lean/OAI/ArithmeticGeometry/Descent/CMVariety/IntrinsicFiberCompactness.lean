import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph

/-! # Intrinsic Fiber Compactness -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
The actual geometric presentation transports compactness and connectedness
to the literal abelian fiber. Connectedness uses the proved HolomorphicAlgebraicity theorem
through the existing native abelian uniformization argument.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

def StandardModuli.Abelian.ComplexAbelianPresentation.nativePointHomeomorph (c : StandardModuli.Abelian.ComplexAbelianPresentation A) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints c.variety.toOver where
  toFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map c.comparison.hom
  invFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map c.comparison.inv
  left_inv x := by
    change (x ≫ c.comparison.hom) ≫ c.comparison.inv = x
    rw [Category.assoc, c.comparison.hom_inv_id, Category.comp_id]
  right_inv x := by
    change (x ≫ c.comparison.inv) ≫ c.comparison.hom = x
    rw [Category.assoc, c.comparison.inv_hom_id, Category.comp_id]
  continuous_toFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _
  continuous_invFun := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _

theorem StandardModuli.Abelian.ComplexAbelianPresentation.compactSpace (c : StandardModuli.Abelian.ComplexAbelianPresentation A) : CompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) := by
  let : CompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints c.variety.toOver) :=
    c.variety.variety.presentation.complexPoints_compactSpace
  exact Function.Surjective.compactSpace c.nativePointHomeomorph.symm.continuous
    c.nativePointHomeomorph.symm.surjective

theorem StandardModuli.Abelian.ComplexAbelianPresentation.connectedSpace (c : StandardModuli.Abelian.ComplexAbelianPresentation A) : ConnectedSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) := by
  let : ConnectedSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints c.variety.toOver) :=
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.native_connectedSpace
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic c.variety
  exact c.nativePointHomeomorph.symm.surjective.connectedSpace c.nativePointHomeomorph.symm.continuous

end

end OAI.ArithmeticGeometry.Descent.CMVariety
