import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SphericalBound
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Smoothness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothExtensionElimination
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductFixedVectors

/-! # Spherical -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Spherical.CM

noncomputable section

/-! The full AdelicTheta prerequisite gives a positive auxiliary-prime bound
and an actual open away level for every prescribed source theta input. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (hAdelicTheta : Adelic.ThetaBall.CM.AdelicThetaInput) (inputs : RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0})

include hAdelicTheta inputs in
theorem exists_bound (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      ∀ (f : E →+* ℚ_[q]) (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q), u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
        Source.FactorTheta.CM.action E L f (u, 1) φ = φ :=
  SmoothExtensionElimination.CM.apply (ThetaRationalTheta.CM.rational E L)
    (Source.WeilData.CM.finiteAction E L)
    (ThetaSmoothExtension.CM.exists_extension E L hAdelicTheta inputs)
    (fun ρ hρ hr => Source.SphericalBound.CM.exists_bound E L ρ hρ hr φ)

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def awayLevel (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) : OpenSubgroup (Source.FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  ProductFixedVectors.CM.awayStabilizer (Source.FactorTheta.CM.action E L f) φ
    (Smoothness.CM.away E L hAdelicTheta inputs f φ)

theorem fixed (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (ha : ∀ u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q, Source.FactorTheta.CM.action E L f (u, 1) φ = φ)
    (a : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q × Source.FactorTheta.CM.RationalWeilFactorization.Away E L f)
    (h : a ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).prod (awayLevel E L hAdelicTheta inputs f φ).toSubgroup) :
    Source.FactorTheta.CM.action E L f a φ = φ :=
  ProductFixedVectors.CM.fixed (Source.FactorTheta.CM.action E L f) φ a.1 a.2 (ha a.1 h.1) h.2

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Spherical.CM
