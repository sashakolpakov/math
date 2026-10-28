import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRealAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaThetaComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.JacobiReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticConjugation

/-! # Theta Jacobi Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaJacobiComparison.CM

noncomputable section

/-! The actual native and source Jacobi changes and Gaussian corrections
commute with the derived source symplectic frame change. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaThetaComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

theorem comp_injective {I J R : Type} (e : I ≃ J) : Function.Injective (fun f : J → R => f ∘ e) := by
  intro f g h
  funext j
  obtain ⟨i, rfl⟩ := e.surjective j
  exact congrFun h i

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

theorem variable_comp (z : B.Domain) (ξ : GeometricSource.CM.Positions E places → ℂ) :
    ThetaThetaComparison.CM.variableChange E L T hT z ξ ∘ ThetaRationalFrame.CM.index E L =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).jacobiChange (L.period z.val) ξ := by
  funext i
  exact congrArg ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).jacobiChange (L.period z.val) ξ)
    ((ThetaRationalFrame.CM.index E L).symm_apply_apply i)

theorem variable_surjective (z : B.Domain) : Function.Surjective (ThetaThetaComparison.CM.variableChange E L T hT z) := by
  intro η
  obtain ⟨ξ, hξ⟩ := SymplecticConjugation.CM.jacobi_surjective
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val) (η ∘ ThetaRationalFrame.CM.index E L)
  exact ⟨ξ, comp_injective (ThetaRationalFrame.CM.index E L) ((variable_comp E L T hT z ξ).trans hξ)⟩

include hG in
theorem jacobi (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) (ξ : GeometricSource.CM.Positions E places → ℂ) :
    (T.symplectic (ThetaArchimedeanAction.CM.rational E L g)).jacobiChange
      (T.period (Source.BallNormalization.CM.equiv E B z)) (ThetaThetaComparison.CM.variableChange E L T hT z ξ) =
      ThetaThetaComparison.CM.variableChange E L T hT
        ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z.val) ξ) := by
  apply comp_injective (ThetaRationalFrame.CM.index E L)
  have hj := JacobiReindex.CM.jacobi (ThetaRationalFrame.CM.index E L)
    (T.symplectic (ThetaArchimedeanAction.CM.rational E L g))
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT * Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g * (ThetaRationalFrame.CM.matrix E L T hT)⁻¹))
    (T.period (Source.BallNormalization.CM.equiv E B z))
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).transformSiegel (L.period z.val))
    (ThetaRealAction.CM.matrix_eq E L T hT g)
    (ThetaPeriodComparison.CM.period_matrix E L T hT hG z)
    (ThetaThetaComparison.CM.variableChange E L T hT z ξ)
  rw [variable_comp E L T hT, SymplecticConjugation.CM.jacobi] at hj
  have hv := variable_comp E L T hT
    ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z.val) ξ)
  have hp := congrArg (fun p : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (GeometricSource.CM.Positions E places) =>
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).jacobiChange p
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z.val) ξ))
    (Source.UnitaryEq.CM.PeriodCovariance.period_covariance E L g z.val z.property)
  exact hj.trans (hp.symm.trans hv.symm)

include hG in
theorem quadratic_native (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain)
    (ξ : GeometricSource.CM.Positions E places → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (T.symplectic (ThetaArchimedeanAction.CM.rational E L g))
      (T.period (Source.BallNormalization.CM.equiv E B z)) (ThetaThetaComparison.CM.variableChange E L T hT z ξ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT * Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g * (ThetaRationalFrame.CM.matrix E L T hT)⁻¹))
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).transformSiegel (L.period z.val))
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).jacobiChange (L.period z.val) ξ) := by
  have hq := JacobiReindex.CM.quadratic (ThetaRationalFrame.CM.index E L)
    (T.symplectic (ThetaArchimedeanAction.CM.rational E L g))
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT * Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g * (ThetaRationalFrame.CM.matrix E L T hT)⁻¹))
    (T.period (Source.BallNormalization.CM.equiv E B z))
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).transformSiegel (L.period z.val))
    (ThetaRealAction.CM.matrix_eq E L T hT g)
    (ThetaPeriodComparison.CM.period_matrix E L T hT hG z)
    (ThetaThetaComparison.CM.variableChange E L T hT z ξ)
  rw [variable_comp E L T hT] at hq
  exact hq

include hG in
theorem quadratic (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain)
    (ξ : GeometricSource.CM.Positions E places → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val) ξ *
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (T.symplectic (ThetaArchimedeanAction.CM.rational E L g))
        (T.period (Source.BallNormalization.CM.equiv E B z)) (ThetaThetaComparison.CM.variableChange E L T hT z ξ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z.val) ξ *
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period (Source.UnitaryEq.CM.Frames.period E g z.val))
          ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z.val) ξ) := by
  rw [quadratic_native E L T hT hG, SymplecticConjugation.CM.quadratic,
    Source.UnitaryEq.CM.PeriodCovariance.period_covariance E L g z.val z.property]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaJacobiComparison.CM
