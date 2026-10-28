import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorSmoothness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RepresentationOpenLevel

/-! # PEL Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELLevel.CM

noncomputable section

/-! An actual source input determines an open PEL level fixing every
source active/away element whose PEL image lies in that level. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
  (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
  (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)

def level (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) : OpenSubgroup P.FiniteSpecialUnitary :=
  RepresentationOpenLevel.CM.transport ρ hρ
    (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb) φ

theorem mem (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (g : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates)) :
    PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb g ∈
        level E L ρ hρ P hb φ ↔ ρ g φ = φ :=
  RepresentationOpenLevel.CM.image_mem ρ hρ _ φ g

include hr in
theorem rational_fixed (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (h : PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb
      (SourceAdelic.ThetaRationalTheta.CM.rational E L γ) ∈ level E L ρ hρ P hb φ) :
    WeilData.CM.finiteAction E L γ φ = φ :=
  (RationalOscillator.CM.action E L ρ hr γ φ).symm.trans
    ((mem E L ρ hρ P hb φ _).mp h)

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

include hr in
theorem product_fixed (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f)
    (h : PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb
      (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a) ∈ level E L ρ hρ P hb φ) :
    FactorTheta.CM.action E L f a φ = φ :=
  (congrArg (fun t : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) => t φ)
    (congrFun (FactorSmoothness.CM.hom E L ρ hρ hr f) a)).trans
      ((mem E L ρ hρ P hb φ _).mp h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELLevel.CM
