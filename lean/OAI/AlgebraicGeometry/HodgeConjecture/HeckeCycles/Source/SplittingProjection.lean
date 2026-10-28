import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.ProjectionTopology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedCoordinateSplitting

/-! # Splitting Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SplittingProjection.CM

noncomputable section

/-! The complete original source splitting projects to the actual
finite unitary product representation. Its action is continuous. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalFactorProjection.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalAwayTopology.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem projection (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (w : FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    (WeilData.CM.weilData E places).finite.project (FactorTheta.CM.RationalWeilFactorization.splitting E L f (a, w)) =
      RationalFactorProjection.CM.productProjection E L f (a, RationalAwayTopology.CM.nativeCoordinates E L f w) :=
  ProjectedCoordinateSplitting.CM.projection (RationalFactorProjection.CM.activeLocal E f)
    (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f) (WeilData.CM.finiteHom E L)
    (FactorTheta.CM.RationalWeilFactorization.remainder_commutes E L f)
    (SourceFinite.Product.CM.awayHom E (OppositeCoordinates.CM.coordinates E L.coordinates) f)
    (WeilData.CM.weilData E places).finite.project (RationalFactorProjection.CM.productProjection E L f)
    (RationalFactorProjection.CM.active_projection E L f) (RationalFactorProjection.CM.rational_projection E L f) a w

theorem continuous_action (v : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Continuous (fun x : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f =>
      ((WeilData.CM.weilData E places).finite.project (FactorTheta.CM.RationalWeilFactorization.splitting E L f x)).val *ᵥ v) := by
  have hc := (SourceFinite.ProjectionTopology.CM.original_action E L.coordinates v).comp
    ((SourceFinite.Topology.CM.equivalence_continuous E
      (OppositeCoordinates.CM.coordinates E L.coordinates) f).comp
        (continuous_fst.prodMk ((RationalAwayCoordinates.CM.native_continuous E L f).comp
          continuous_snd)))
  exact hc.congr (fun x => congrArg (fun M : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => M.val *ᵥ v)
    (projection E L f x.1 x.2).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SplittingProjection.CM
