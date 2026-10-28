import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaSmoothExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.ProjectionTopology

/-! # Rational Oscillator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalOscillator.CM

noncomputable section

/-! The source rational action has the exact unitary and Heisenberg
identities for the independently constructed finite symplectic projection. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
  (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)

include hr in
theorem action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ρ (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g) φ =
      (WeilData.CM.weilData E places).finite.action (WeilData.CM.finiteHom E L g) φ :=
  congrArg (fun a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) => a φ)
    (DFunLike.congr_fun hr g)

theorem projection (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (WeilData.CM.weilData E places).finite.project (WeilData.CM.finiteHom E L g) =
      ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g) :=
  (SourceFinite.FiniteLift.CM.finiteLift_covers E L (WeilData.CM.weilData E places) g).trans
    (ReferenceActiveWeil.CM.ReferenceFiniteProjection.rational E L.coordinates g).symm

include hr in
theorem unitary (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    Finite.FiniteOscillator.CM.integralPairing
      (ρ (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g) φ)
      (ρ (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g) ψ) =
        Finite.FiniteOscillator.CM.integralPairing φ ψ :=
  (congrArg₂ Finite.FiniteOscillator.CM.integralPairing (CM.action E L ρ hr g φ) (CM.action E L ρ hr g ψ)).trans
    (WeilReindexBare.CM.FiniteOscillator.unitary (GeometricSource.CM.Positions E places) (WeilData.CM.finiteHom E L g) φ ψ)

include hr in
theorem covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (v : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ρ (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g)
      (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) φ) =
    Finite.FourierHeisenberg.CM.operator
      (fun i => ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g)).val *ᵥ v) (.inl i))
      (fun i => ((ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g)).val *ᵥ v) (.inr i))
      (ρ (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g) φ) := by
  refine (CM.action E L ρ hr g _).trans
    ((WeilReindexBare.CM.FiniteOscillator.covariance (GeometricSource.CM.Positions E places) (WeilData.CM.finiteHom E L g) v φ).trans ?_)
  exact congrArg₂ (fun s : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) =>
    Finite.FourierHeisenberg.CM.operator (fun i => (s.val *ᵥ v) (.inl i)) (fun i => (s.val *ᵥ v) (.inr i)) f)
    (projection E L g) (CM.action E L ρ hr g φ).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalOscillator.CM
