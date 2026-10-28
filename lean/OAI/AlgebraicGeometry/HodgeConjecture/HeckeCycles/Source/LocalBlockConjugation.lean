import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.LocalBlocks
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixContinuity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.ProjectionTopology
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteConjugation

/-! # Local Block Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalBlockConjugation.CM

noncomputable section

/-! Continuity extends the rational source block identity to its full
actual active/away product, with the same source frame and matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime]
  (f : E →+* ℚ_[q]) (τ : Fin places.count → E →+* ℚ_[q])
  {n : ℕ} (c : GeometricSource.CM.Positions E places ≃ Fin n) (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ_[q])

theorem conjugation
    (hr : ∀ g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b,
      S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) * S⁻¹ =
        CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (fun i => Matrix.SpecialLinearGroup.map (τ i) g.val))
    (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a)) * S⁻¹ =
      CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (SourceFinite.LocalBlocks.CM.blocks E f L τ a) := by
  have hc : Continuous (fun a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] ×
      FactorTheta.CM.RationalWeilFactorization.Away E L f =>
      (S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
        (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
          (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a)) * S⁻¹).val) :=
    (continuous_const.matrix_mul (Local.MatrixContinuity.CM.padic _
      (Local.MatrixContinuity.CM.of_action _ (fun v =>
        (SourceFinite.ProjectionTopology.CM.original_action E L.coordinates v).comp
          (IntrinsicActiveClosure.CM.Intrinsic.continuous E L f))))).matrix_mul continuous_const
  have he := (RationalDensity.CM.dense E L f).equalizer hc
    (Local.MatrixContinuity.CM.blocks c _ (SourceFinite.LocalBlocks.CM.blocks_continuous E f L τ))
    (funext (fun g => by
      have hsource := (congrArg (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates)
        (IntrinsicActiveClosure.CM.Intrinsic.rational E L f g)).trans
          (ReferenceActiveWeil.CM.ReferenceFiniteProjection.rational E L.coordinates g)
      have hlocal := (congrArg (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom) hsource).trans
        (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.rationalSymplectic_finite_projection q (ComplexAction.CM.Symplectic.symplectic E L.coordinates g))
      exact congrArg Subtype.val
        ((congrArg (fun z : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ_[q] => S * z * S⁻¹) hlocal).trans
          ((hr g).trans (congrArg (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c)
            (SourceFinite.LocalBlocks.CM.blocks_rational E f L τ g)).symm))))
  exact Subtype.ext (congrFun he a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalBlockConjugation.CM
