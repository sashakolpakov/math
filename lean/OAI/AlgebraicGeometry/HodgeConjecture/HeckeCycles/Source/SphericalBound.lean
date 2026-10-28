import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnramifiedBound
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorSmoothness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeBounds

/-! # Spherical Bound -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SphericalBound.CM

noncomputable section

/-! The actual prescribed source finite Schwartz input is fixed by the
standard integral active SL3 subgroup outside one rational-prime bound. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
  (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
  (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem assemble_active (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1) =
      RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
        (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
        (QadicPlace.CM.place E f)
        ((QadicSpecialLinear.CM.equivalence E
          (OppositeCoordinates.CM.coordinates E L.coordinates) f).symm u) := by
  refine (IntrinsicActiveClosure.CM.Intrinsic.active E L f u).trans ?_
  exact (SourceFinite.Product.CM.equivalence_apply E
    (OppositeCoordinates.CM.coordinates E L.coordinates) f u 1).trans (mul_one _)

include hρ hr in
theorem active_fixed (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (hgood : SplitIntegralLocal.CM.Good (QuadraticConjugation.CM.Field.RealField E)
      (QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (QadicPlace.CM.place E f))
    (hfix : ∀ g ∈ SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates)
        (QadicPlace.CM.place E f),
      ρ (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
        (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
        (QadicPlace.CM.place E f) g) φ = φ)
    (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hu : u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    FactorTheta.CM.action E L f (u, 1) φ = φ := by
  have he := congrArg (fun a : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ]
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) => a φ)
    (congrFun (FactorSmoothness.CM.hom E L ρ hρ hr f) (u, 1))
  exact he.trans ((congrArg (fun g => ρ g φ) (assemble_active E L f u)).trans
    (hfix _ (QadicIntegral.CM.inverse_integral E
      (OppositeCoordinates.CM.coordinates E L.coordinates) f hgood u hu)))

include hρ hr in
theorem exists_bound (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      ∀ (f : E →+* ℚ_[q]) (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q), u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
        FactorTheta.CM.action E L f (u, 1) φ = φ := by
  exact PrimeBounds.CM.combine _ _ _
    (UnramifiedBound.CM.exists_bound E L ρ hρ φ)
    (QadicIntegral.CM.exists_good_bound E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (fun _ _ hf hg f u hu => active_fixed E L ρ hρ hr f φ (hg f) (hf f) u hu)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SphericalBound.CM
