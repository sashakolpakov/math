import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.UnitaryPresentation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.MultiplicityOne

/-! # One Unitary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary.Quadratic

noncomputable section

/-! The original rational unitary group in the actual AdelicTheta matrix model.
Its local matrices use the original CM embeddings, entry by entry. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)

theorem cmHermitianUnit_diagonal :
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val =
      UnitaryMatrixEquiv.Quadratic.diagonalForm ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm b) := by
  rw [ThetaCycle.CMGlobalFrames.CM.cm_hermitian_unit_val E δ hδ hδ0]
  unfold ThetaCycle.QuadraticTensor.CM.quadraticHermitianMatrix UnitaryMatrixEquiv.Quadratic.diagonalForm Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient
  congr 1
  funext j
  split_ifs <;> simp

def cmRationalUnitaryPresentation :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val :=
  ((Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.unitaryEquiv (IsCMField.complexConj E).toRingHom (starRingEnd _) b
      (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm.toRingEquiv
      (fun x => ThetaCycle.QuadraticModel.CM.cm_quadratic_equiv_conjugation E δ hδ hδ0 x)).trans
    (UnitaryMatrixEquiv.Quadratic.unitaryMatrixEquiv ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm b))).trans
      (CM.UnitaryPresentation.Quadratic.unitaryFormCongr _ _ (cmHermitianUnit_diagonal E δ hδ hδ0 b hb hb0).symm)

theorem cmRationalUnitaryPresentation_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    (cmRationalUnitaryPresentation E δ hδ hδ0 b hb hb0 g).val.val =
      g.val.val.map (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm := rfl

variable [IsGalois ℚ E] (places : HeckeCycles.GeometricSource.CM.Places E)

theorem cmRationalUnitaryPresentation_arch (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) (i : Fin places.count) :
    ((RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E)
      (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
      (cmRationalUnitaryPresentation E δ hδ hδ0 b hb hb0 g)
      (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places i)).val.val.map
        (ThetaCycle.CMArchimedeanCoordinates.CM.sourceComplexCoordinate E places δ hδ hδ0 i)) =
      g.val.val.map (HeckeCycles.ReferenceDatum.CM.embeddings E places i) := by
  apply Matrix.ext
  intro j k
  change ThetaCycle.CMArchimedeanCoordinates.CM.sourceComplexCoordinate E places δ hδ hδ0 i
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal _ _ _
      ((cmRationalUnitaryPresentation E δ hδ hδ0 b hb hb0 g).val.val j k)) = _
  rw [ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_rational, cmRationalUnitaryPresentation_matrix,
    Matrix.map_apply, AlgEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary.Quadratic
