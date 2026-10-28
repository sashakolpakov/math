import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveWeil
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilConjugatedHom

/-! # Reference Active Weil -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceActiveWeil.CM.Reference

/-! Return the constructed active metaplectic action to the original
source polarization using an actual rational Weil lift of the proved frame change. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def frameLift : WeilData.CM.FiniteCoverGroup E places :=
  (WeilData.CM.weilData E places).finiteLift (OrientedTraceFrame.CM.matrix E C)

theorem frame_projection :
    (WeilData.CM.weilData E places).finite.project (frameLift E C) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C) :=
  (WeilData.CM.weilData E places).finiteLift_covers _

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def lift : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →* WeilData.CM.FiniteCoverGroup E places :=
  WeilConjugatedHom.CM.conjugated (frameLift E C) (ActiveWeil.CM.lift E C f)

theorem projection (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    (WeilData.CM.weilData E places).finite.project (lift E C f g) =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C))⁻¹ *
        (WeilData.CM.weilData E places).finite.project (ActiveWeil.CM.lift E C f g) *
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C) := by
  have h := WeilConjugatedHom.CM.projection (WeilData.CM.weilData E places)
    (frameLift E C) (ActiveWeil.CM.lift E C f) g
  rw [frame_projection] at h
  exact h

theorem action (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    (WeilData.CM.weilData E places).finite.action (frameLift E C)
      ((WeilData.CM.weilData E places).finite.action (lift E C f g) φ) =
      TraceAction.CM.productAction E (OppositeCoordinates.CM.coordinates E C) f (g, 1)
        ((WeilData.CM.weilData E places).finite.action (frameLift E C) φ) :=
  (WeilConjugatedHom.CM.action (WeilData.CM.weilData E places)
    (frameLift E C) (ActiveWeil.CM.lift E C f) g φ).trans (ActiveWeil.CM.action E C f g _)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceActiveWeil.CM.Reference

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceActiveWeil.CM.ReferenceFiniteProjection

/-! The full actual finite symplectic representation in the original
source polarization, with exact rational and active restrictions. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def projection : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C) →*
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  (MulAut.conj (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C))⁻¹).toMonoidHom.comp
    (SourceFinite.Projection.CM.projection E C)

theorem rational (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    projection E C (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ComplexAction.CM.Symplectic.symplectic E C g) := by
  change (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C))⁻¹ *
    SourceFinite.Projection.CM.projection E C
      (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g) *
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C))⁻¹⁻¹ = _
  rw [SourceFinite.Projection.CM.rational_projection, inv_inv, map_mul, map_mul, map_inv]
  group

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem active (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    (WeilData.CM.weilData E places).finite.project (Reference.lift E C f g) =
      projection E C (ActiveMetaplectic.CM.inclusion E C f g) := by
  have h : (WeilData.CM.weilData E places).finite.project (ActiveWeil.CM.lift E C f g) =
      SourceFinite.Projection.CM.projection E C (ActiveMetaplectic.CM.inclusion E C f g) :=
    Subtype.ext (ActiveWeil.CM.projection_matrix E C f g)
  refine (Reference.projection E C f g).trans
    ((congrArg (fun x =>
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C))⁻¹ * x *
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C)) h).trans ?_)
  exact (WeilConjugatedHom.CM.value
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (OrientedTraceFrame.CM.matrix E C))
    (SourceFinite.Projection.CM.projection E C) (ActiveMetaplectic.CM.inclusion E C f g)).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceActiveWeil.CM.ReferenceFiniteProjection

end

end OAI
